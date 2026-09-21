let range name array_length pos_arg len_arg =
  let pos = match pos_arg with None -> 0 | Some pos -> pos in
  if pos < 0 || pos > array_length then invalid_arg (name ^ ": invalid range");
  let len = match len_arg with None -> array_length - pos | Some len -> len in
  if len < 0 || len > array_length - pos then
    invalid_arg (name ^ ": invalid range");
  (pos, len)

let recommended_domains () = max 1 (Domain.recommended_domain_count ())

let digit_bits = 11
let max_radix = 1 lsl digit_bits
let parallel_cutoff = 262_144
let target_chunk_size = 131_072

let choose_workers domains len =
  let requested =
    match domains with
    | None -> recommended_domains ()
    | Some domains ->
        if domains < 1 then invalid_arg "Radix_sort_domain: domains < 1";
        domains
  in
  if len < parallel_cutoff then 1
  else
    let useful = 1 + ((len - 1) / target_chunk_size) in
    min requested useful

let chunk len workers worker =
  let quotient = len / workers in
  let remainder = len mod workers in
  let before = min worker remainder in
  let lo = (worker * quotient) + before in
  let size = quotient + if worker < remainder then 1 else 0 in
  (lo, lo + size)

let run workers f =
  let spawned =
    Array.init (workers - 1) (fun i -> Domain.spawn (fun () -> f (i + 1)))
  in
  f 0;
  Array.iter (fun domain -> Domain.join domain) spawned

let make_worker_tables workers =
  Array.init workers (fun _ -> Array.make max_radix 0)

let prepare_offsets histograms offsets workers radix =
  let target = ref 0 in
  for d = 0 to radix - 1 do
    for worker = 0 to workers - 1 do
      offsets.(worker).(d) <- !target;
      target := !target + histograms.(worker).(d)
    done
  done

module Int = struct
  let sort ?domains ?pos ?len a =
    let pos, len =
      range "Radix_sort_domain.Int.sort" (Array.length a) pos len
    in
    let workers = choose_workers domains len in
    if workers = 1 then Radix_sort.Int.sort ~pos ~len a
    else begin
      let first = a.(pos) lxor min_int in
      let varying = ref 0 in
      for i = pos + 1 to pos + len - 1 do
        varying := !varying lor ((a.(i) lxor min_int) lxor first)
      done;
      if !varying <> 0 then begin
        let tmp = Array.make len 0 in
        let histograms = make_worker_tables workers in
        let offsets = make_worker_tables workers in
        let source_is_a = ref true in
        let shift = ref 0 in
        while !shift < Sys.int_size do
          let bits = min digit_bits (Sys.int_size - !shift) in
          let radix = 1 lsl bits in
          let mask = radix - 1 in
          if ((!varying lsr !shift) land mask) <> 0 then begin
            let from_a = !source_is_a in
            run workers (fun worker ->
                let histogram = histograms.(worker) in
                Array.fill histogram 0 radix 0;
                let lo, hi = chunk len workers worker in
                if from_a then
                  for i = lo to hi - 1 do
                    let d =
                      ((a.(pos + i) lxor min_int) lsr !shift) land mask
                    in
                    histogram.(d) <- histogram.(d) + 1
                  done
                else
                  for i = lo to hi - 1 do
                    let d = ((tmp.(i) lxor min_int) lsr !shift) land mask in
                    histogram.(d) <- histogram.(d) + 1
                  done);
            prepare_offsets histograms offsets workers radix;
            run workers (fun worker ->
                let next = offsets.(worker) in
                let lo, hi = chunk len workers worker in
                if from_a then
                  for i = lo to hi - 1 do
                    let value = a.(pos + i) in
                    let d = ((value lxor min_int) lsr !shift) land mask in
                    let target = next.(d) in
                    tmp.(target) <- value;
                    next.(d) <- target + 1
                  done
                else
                  for i = lo to hi - 1 do
                    let value = tmp.(i) in
                    let d = ((value lxor min_int) lsr !shift) land mask in
                    let target = next.(d) in
                    a.(pos + target) <- value;
                    next.(d) <- target + 1
                  done);
            source_is_a := not !source_is_a
          end;
          shift := !shift + bits
        done;
        if not !source_is_a then Array.blit tmp 0 a pos len
      end
    end
end

module I64 = Stdlib.Int64

module Int64 = struct
  let[@inline] key value = I64.logxor value I64.min_int

  let[@inline] digit value shift mask =
    let raw = I64.to_int (I64.shift_right_logical value shift) land mask in
    if shift = 55 then raw lxor 256 else raw

  let sort ?domains ?pos ?len a =
    let pos, len =
      range "Radix_sort_domain.Int64.sort" (Array.length a) pos len
    in
    let workers = choose_workers domains len in
    if workers = 1 then Radix_sort.Int64.sort ~pos ~len a
    else begin
      let first = key a.(pos) in
      let varying = ref 0L in
      for i = pos + 1 to pos + len - 1 do
        varying := I64.logor !varying (I64.logxor (key a.(i)) first)
      done;
      if !varying <> 0L then begin
        let tmp = Array.make len 0L in
        let histograms = make_worker_tables workers in
        let offsets = make_worker_tables workers in
        let source_is_a = ref true in
        let shift = ref 0 in
        while !shift < 64 do
          let bits = min digit_bits (64 - !shift) in
          let radix = 1 lsl bits in
          let mask = radix - 1 in
          let changed =
            I64.logand (I64.shift_right_logical !varying !shift)
              (I64.of_int mask)
          in
          if changed <> 0L then begin
            let from_a = !source_is_a in
            run workers (fun worker ->
                let histogram = histograms.(worker) in
                Array.fill histogram 0 radix 0;
                let lo, hi = chunk len workers worker in
                if from_a then
                  for i = lo to hi - 1 do
                    let d = digit a.(pos + i) !shift mask in
                    histogram.(d) <- histogram.(d) + 1
                  done
                else
                  for i = lo to hi - 1 do
                    let d = digit tmp.(i) !shift mask in
                    histogram.(d) <- histogram.(d) + 1
                  done);
            prepare_offsets histograms offsets workers radix;
            run workers (fun worker ->
                let next = offsets.(worker) in
                let lo, hi = chunk len workers worker in
                if from_a then
                  for i = lo to hi - 1 do
                    let value = a.(pos + i) in
                    let d = digit value !shift mask in
                    let target = next.(d) in
                    tmp.(target) <- value;
                    next.(d) <- target + 1
                  done
                else
                  for i = lo to hi - 1 do
                    let value = tmp.(i) in
                    let d = digit value !shift mask in
                    let target = next.(d) in
                    a.(pos + target) <- value;
                    next.(d) <- target + 1
                  done);
            source_is_a := not !source_is_a
          end;
          shift := !shift + bits
        done;
        if not !source_is_a then Array.blit tmp 0 a pos len
      end
    end
end

module Float = struct
  let[@inline] key value =
    let bits = I64.bits_of_float value in
    if bits < 0L then I64.lognot bits else I64.logxor bits I64.min_int

  let[@inline] digit value shift mask =
    let bits = I64.bits_of_float value in
    let raw = I64.to_int (I64.shift_right_logical bits shift) land mask in
    if bits < 0L then raw lxor mask
    else if shift = 55 then raw lxor 256
    else raw

  let sort ?domains ?pos ?len a =
    let pos, len =
      range "Radix_sort_domain.Float.sort" (Array.length a) pos len
    in
    let workers = choose_workers domains len in
    if workers = 1 then Radix_sort.Float.sort ~pos ~len a
    else begin
      let first = key a.(pos) in
      let varying = ref 0L in
      for i = pos + 1 to pos + len - 1 do
        varying := I64.logor !varying (I64.logxor (key a.(i)) first)
      done;
      if !varying <> 0L then begin
        let tmp = Array.make len 0. in
        let histograms = make_worker_tables workers in
        let offsets = make_worker_tables workers in
        let source_is_a = ref true in
        let shift = ref 0 in
        while !shift < 64 do
          let bits = min digit_bits (64 - !shift) in
          let radix = 1 lsl bits in
          let mask = radix - 1 in
          let changed =
            I64.logand (I64.shift_right_logical !varying !shift)
              (I64.of_int mask)
          in
          if changed <> 0L then begin
            let from_a = !source_is_a in
            run workers (fun worker ->
                let histogram = histograms.(worker) in
                Array.fill histogram 0 radix 0;
                let lo, hi = chunk len workers worker in
                if from_a then
                  for i = lo to hi - 1 do
                    let d = digit a.(pos + i) !shift mask in
                    histogram.(d) <- histogram.(d) + 1
                  done
                else
                  for i = lo to hi - 1 do
                    let d = digit tmp.(i) !shift mask in
                    histogram.(d) <- histogram.(d) + 1
                  done);
            prepare_offsets histograms offsets workers radix;
            run workers (fun worker ->
                let next = offsets.(worker) in
                let lo, hi = chunk len workers worker in
                if from_a then
                  for i = lo to hi - 1 do
                    let value = a.(pos + i) in
                    let d = digit value !shift mask in
                    let target = next.(d) in
                    tmp.(target) <- value;
                    next.(d) <- target + 1
                  done
                else
                  for i = lo to hi - 1 do
                    let value = tmp.(i) in
                    let d = digit value !shift mask in
                    let target = next.(d) in
                    a.(pos + target) <- value;
                    next.(d) <- target + 1
                  done);
            source_is_a := not !source_is_a
          end;
          shift := !shift + bits
        done;
        if not !source_is_a then Array.blit tmp 0 a pos len
      end
    end
end
