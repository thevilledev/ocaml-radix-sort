let range name array_length pos_arg len_arg =
  let pos = match pos_arg with None -> 0 | Some pos -> pos in
  if pos < 0 || pos > array_length then invalid_arg (name ^ ": invalid range");
  let len = match len_arg with None -> array_length - pos | Some len -> len in
  if len < 0 || len > array_length - pos then
    invalid_arg (name ^ ": invalid range");
  (pos, len)

let digit_bits = 11
let max_radix = 1 lsl digit_bits

module Int = struct
  let sort ?pos ?len a =
    let pos, len = range "Radix_sort.Int.sort" (Array.length a) pos len in
    if len > 1 then begin
      let first = a.(pos) lxor min_int in
      let varying = ref 0 in
      for i = pos + 1 to pos + len - 1 do
        varying := !varying lor ((a.(i) lxor min_int) lxor first)
      done;
      if !varying <> 0 then begin
        let tmp = Array.make len 0 in
        let counts = Array.make max_radix 0 in
        let source_is_a = ref true in
        let shift = ref 0 in
        while !shift < Sys.int_size do
          let bits = min digit_bits (Sys.int_size - !shift) in
          let radix = 1 lsl bits in
          let mask = radix - 1 in
          if ((!varying lsr !shift) land mask) <> 0 then begin
            Array.fill counts 0 radix 0;
            if !source_is_a then
              for i = 0 to len - 1 do
                let d = ((a.(pos + i) lxor min_int) lsr !shift) land mask in
                counts.(d) <- counts.(d) + 1
              done
            else
              for i = 0 to len - 1 do
                let d = ((tmp.(i) lxor min_int) lsr !shift) land mask in
                counts.(d) <- counts.(d) + 1
              done;
            let total = ref 0 in
            for d = 0 to radix - 1 do
              let count = counts.(d) in
              counts.(d) <- !total;
              total := !total + count
            done;
            if !source_is_a then
              for i = 0 to len - 1 do
                let value = a.(pos + i) in
                let d = ((value lxor min_int) lsr !shift) land mask in
                let target = counts.(d) in
                tmp.(target) <- value;
                counts.(d) <- target + 1
              done
            else
              for i = 0 to len - 1 do
                let value = tmp.(i) in
                let d = ((value lxor min_int) lsr !shift) land mask in
                let target = counts.(d) in
                a.(pos + target) <- value;
                counts.(d) <- target + 1
              done;
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

  let sort ?pos ?len a =
    let pos, len = range "Radix_sort.Int64.sort" (Array.length a) pos len in
    if len > 1 then begin
      let first = key a.(pos) in
      let varying = ref 0L in
      for i = pos + 1 to pos + len - 1 do
        varying := I64.logor !varying (I64.logxor (key a.(i)) first)
      done;
      if !varying <> 0L then begin
        let tmp = Array.make len 0L in
        let counts = Array.make max_radix 0 in
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
            Array.fill counts 0 radix 0;
            if !source_is_a then
              for i = 0 to len - 1 do
                let d = digit a.(pos + i) !shift mask in
                counts.(d) <- counts.(d) + 1
              done
            else
              for i = 0 to len - 1 do
                let d = digit tmp.(i) !shift mask in
                counts.(d) <- counts.(d) + 1
              done;
            let total = ref 0 in
            for d = 0 to radix - 1 do
              let count = counts.(d) in
              counts.(d) <- !total;
              total := !total + count
            done;
            if !source_is_a then
              for i = 0 to len - 1 do
                let value = a.(pos + i) in
                let d = digit value !shift mask in
                let target = counts.(d) in
                tmp.(target) <- value;
                counts.(d) <- target + 1
              done
            else
              for i = 0 to len - 1 do
                let value = tmp.(i) in
                let d = digit value !shift mask in
                let target = counts.(d) in
                a.(pos + target) <- value;
                counts.(d) <- target + 1
              done;
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

  let compare a b =
    I64.compare (I64.logxor (key a) I64.min_int)
      (I64.logxor (key b) I64.min_int)

  let[@inline] digit value shift mask =
    let bits = I64.bits_of_float value in
    let raw = I64.to_int (I64.shift_right_logical bits shift) land mask in
    if bits < 0L then raw lxor mask
    else if shift = 55 then raw lxor 256
    else raw

  let sort ?pos ?len a =
    let pos, len = range "Radix_sort.Float.sort" (Array.length a) pos len in
    if len > 1 then begin
      let first = key a.(pos) in
      let varying = ref 0L in
      for i = pos + 1 to pos + len - 1 do
        varying := I64.logor !varying (I64.logxor (key a.(i)) first)
      done;
      if !varying <> 0L then begin
        let tmp = Array.make len 0. in
        let counts = Array.make max_radix 0 in
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
            Array.fill counts 0 radix 0;
            if !source_is_a then
              for i = 0 to len - 1 do
                let d = digit a.(pos + i) !shift mask in
                counts.(d) <- counts.(d) + 1
              done
            else
              for i = 0 to len - 1 do
                let d = digit tmp.(i) !shift mask in
                counts.(d) <- counts.(d) + 1
              done;
            let total = ref 0 in
            for d = 0 to radix - 1 do
              let count = counts.(d) in
              counts.(d) <- !total;
              total := !total + count
            done;
            if !source_is_a then
              for i = 0 to len - 1 do
                let value = a.(pos + i) in
                let d = digit value !shift mask in
                let target = counts.(d) in
                tmp.(target) <- value;
                counts.(d) <- target + 1
              done
            else
              for i = 0 to len - 1 do
                let value = tmp.(i) in
                let d = digit value !shift mask in
                let target = counts.(d) in
                a.(pos + target) <- value;
                counts.(d) <- target + 1
              done;
            source_is_a := not !source_is_a
          end;
          shift := !shift + bits
        done;
        if not !source_is_a then Array.blit tmp 0 a pos len
      end
    end
end

module String = struct
  let buckets = 257
  let insertion_cutoff = 24

  let digit value depth =
    if depth = Stdlib.String.length value then 0
    else Char.code (Stdlib.String.unsafe_get value depth) + 1

  let insertion_sort a lo len =
    for i = lo + 1 to lo + len - 1 do
      let value = a.(i) in
      let j = ref (i - 1) in
      while !j >= lo && Stdlib.String.compare a.(!j) value > 0 do
        a.(!j + 1) <- a.(!j);
        decr j
      done;
      a.(!j + 1) <- value
    done

  let sort ?pos ?len a =
    let pos, len = range "Radix_sort.String.sort" (Array.length a) pos len in
    if len > 1 then begin
      let counts = Array.make buckets 0 in
      let starts = Array.make buckets 0 in
      let next = Array.make buckets 0 in
      let pending = ref [pos, len, 0] in
      while !pending <> [] do
        match !pending with
        | [] -> assert false
        | (lo, count, depth) :: rest ->
            pending := rest;
            if count <= insertion_cutoff then insertion_sort a lo count
            else begin
              Array.fill counts 0 buckets 0;
              for i = lo to lo + count - 1 do
                let d = digit a.(i) depth in
                counts.(d) <- counts.(d) + 1
              done;
              starts.(0) <- lo;
              for d = 1 to buckets - 1 do
                starts.(d) <- starts.(d - 1) + counts.(d - 1)
              done;
              Array.blit starts 0 next 0 buckets;
              for bucket = 0 to buckets - 1 do
                let finish = starts.(bucket) + counts.(bucket) in
                while next.(bucket) < finish do
                  let i = next.(bucket) in
                  let value = a.(i) in
                  let target_bucket = digit value depth in
                  if target_bucket = bucket then
                    next.(bucket) <- i + 1
                  else begin
                    let target = next.(target_bucket) in
                    let displaced = a.(target) in
                    a.(target) <- value;
                    a.(i) <- displaced;
                    next.(target_bucket) <- target + 1
                  end
                done
              done;
              for bucket = buckets - 1 downto 1 do
                let bucket_count = counts.(bucket) in
                if bucket_count > 1 then
                  pending :=
                    (starts.(bucket), bucket_count, depth + 1) :: !pending
              done
            end
      done
    end
end
