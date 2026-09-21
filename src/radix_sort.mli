(** Radix sorts that mutate the selected array slice.

    All sorts accept [pos] (default [0]) and [len] (default remaining length).
    Elements outside the slice are unchanged. Invalid ranges raise
    [Invalid_argument]: [pos] must be in [0..Array.length a] and [len] in
    [0..Array.length a - pos].

    Numeric sorts are stable LSD sorts with 11-bit digits and constant-pass
    skipping. Workspace: up to one slice-sized array plus 2,048 counters. *)

module Int : sig
  val sort : ?pos:int -> ?len:int -> int array -> unit
  (** Stable signed ascending sort; supports 31- and 63-bit OCaml integers. *)
end

module Int64 : sig
  val sort : ?pos:int -> ?len:int -> int64 array -> unit
  (** Stable signed ascending sort of 64-bit integers. *)
end

module Float : sig
  val compare : float -> float -> int
  (** The bit-pattern order used by {!sort}; zero only for identical bits. *)

  val sort : ?pos:int -> ?len:int -> float array -> unit
  (** Stable sort of an unboxed float array, preserving all bit patterns.

      Order: negative NaNs, negative infinity, finite numbers, positive
      infinity, positive NaNs; [-0.] precedes [+0.]. Unlike [Stdlib.compare],
      this distinguishes NaN payloads and signed zeros.

      Keys compare as unsigned 64-bit integers: complement every bit of
      negative encodings; flip the sign bit of non-negative encodings. *)
end

module String : sig
  val sort : ?pos:int -> ?len:int -> string array -> unit
  (** Unstable, in-place MSD/American-flag sort in [Stdlib.String.compare]
      order. Uses fixed histograms and an explicit work stack; long common
      prefixes do not grow the call stack. *)
end
