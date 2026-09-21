(** Stable parallel radix sorts for OCaml 5, using local histograms and
    parallel scattering. Ordering and slice contracts match {!Radix_sort}.

    [domains] caps workers including the caller; defaults to
    {!recommended_domains}. Values below [1] raise [Invalid_argument]. Small
    inputs use the sequential sort. Workspace: up to one slice-sized array
    plus per-worker histograms. *)

val recommended_domains : unit -> int
(** [max 1 (Domain.recommended_domain_count ())]. *)

module Int : sig
  val sort : ?domains:int -> ?pos:int -> ?len:int -> int array -> unit
  (** Parallel {!Radix_sort.Int.sort}. *)
end

module Int64 : sig
  val sort : ?domains:int -> ?pos:int -> ?len:int -> int64 array -> unit
  (** Parallel {!Radix_sort.Int64.sort}. *)
end

module Float : sig
  val sort : ?domains:int -> ?pos:int -> ?len:int -> float array -> unit
  (** Parallel {!Radix_sort.Float.sort}. *)
end
