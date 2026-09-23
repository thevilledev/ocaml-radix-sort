-------------------------- MODULE ParallelRadixSort --------------------------
(***************************************************************************)
(* Model of the parallel LSD radix sort in                                  *)
(* src/domain/radix_sort_domain.ml (Int.sort, lines 56-124; Int64.sort and  *)
(* Float.sort, lines 128-287, have exactly the same control structure and   *)
(* differ only in how a key/digit is extracted from a value).               *)
(*                                                                          *)
(* Keys are abstract unsigned KeyBits-bit integers: the "lxor min_int" /    *)
(* Int64/Float key maps of the OCaml code are order-preserving bijections   *)
(* onto unsigned integers and are verified separately (Lean).  Every array  *)
(* element is a pair <<key, id>> where id is the element's original index, *)
(* so stability can be checked.                                            *)
(*                                                                          *)
(* The model starts after choose_workers has returned Workers >= 1 (only    *)
(* Workers >= 2 reaches this code in OCaml; Workers = 1 is allowed here to  *)
(* compare with the sequential structure) and uses pos = 0, so the model's  *)
(* array is the sorted slice.                                               *)
(*                                                                          *)
(* Processes: the caller ("main", also running f 0 and, in the fixed run    *)
(* variant, the chunks of workers that could not be spawned) and spawned    *)
(* domains 1..Workers-1, domain d always running f d.  Every iteration of   *)
(* every worker "for" loop is one atomic step, so TLC explores all          *)
(* interleavings of the caller with the spawned domains.                    *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS
    N,              \* slice length (len)
    KeyBits,        \* key width (Sys.int_size = 63 / 64 in OCaml)
    DigitBits,      \* digit_bits (11 in OCaml)
    Workers,        \* result of choose_workers
    RunVariant,     \* "original" = run as in the OCaml; "fixed" = proposed fix
    SpawnCanFail,   \* Domain.spawn may raise Failure
    CallerCanRaise  \* an asynchronous exception may be raised inside the
                    \* caller's own chunk (f 0 or a caller-run chunk)

ASSUME /\ N \in Nat \ {0}
       /\ KeyBits \in Nat \ {0}
       /\ DigitBits \in Nat \ {0}
       /\ Workers \in Nat \ {0}
       /\ RunVariant \in {"original", "fixed"}
       /\ SpawnCanFail \in BOOLEAN
       /\ CallerCanRaise \in BOOLEAN

W         == Workers
Idx       == 0 .. N - 1
WorkerIds == 0 .. W - 1
Domains   == 1 .. W - 1
MaxKey    == 2^KeyBits - 1
MaxRadix  == 2^DigitBits          \* max_radix = 1 lsl digit_bits (line 12)
Digits    == 0 .. MaxRadix - 1    \* indices of a worker table
Bufs      == {"a", "tmp"}

Key(e) == e[1]
Id(e)  == e[2]
Zero   == <<0, -1>>                \* the filler of Array.make len 0 (line 70)
Elem   == (0 .. MaxKey) \X (-1 .. N - 1)

Min(x, y) == IF x < y THEN x ELSE y

(***************************************************************************)
(* Bitwise operations on naturals (OCaml lxor, lor, land, lsr).            *)
(***************************************************************************)
RECURSIVE BitXor(_, _), BitOr(_, _), BitAnd(_, _)
BitXor(x, y) == IF x = 0 /\ y = 0 THEN 0
                ELSE (((x % 2) + (y % 2)) % 2) + 2 * BitXor(x \div 2, y \div 2)
BitOr(x, y)  == IF x = 0 /\ y = 0 THEN 0
                ELSE (IF x % 2 = 1 \/ y % 2 = 1 THEN 1 ELSE 0)
                     + 2 * BitOr(x \div 2, y \div 2)
BitAnd(x, y) == IF x = 0 \/ y = 0 THEN 0
                ELSE (IF x % 2 = 1 /\ y % 2 = 1 THEN 1 ELSE 0)
                     + 2 * BitAnd(x \div 2, y \div 2)
Lsr(x, s)    == x \div 2^s

(* Lines 64-68: first = key a.(pos); varying |= key a.(i) lxor first.      *)
RECURSIVE VaryingLoop(_, _, _)
VaryingLoop(arr, i, acc) ==
    IF i > N - 1 THEN acc
    ELSE VaryingLoop(arr, i + 1, BitOr(acc, BitXor(Key(arr[i]), Key(arr[0]))))
Varying(arr) == VaryingLoop(arr, 1, 0)

(* Lines 29-35: chunk len workers worker.                                  *)
Chunk(len, workers, worker) ==
    LET quotient  == len \div workers
        remainder == len % workers
        before    == Min(worker, remainder)
        lo        == (worker * quotient) + before
        size      == quotient + (IF worker < remainder THEN 1 ELSE 0)
    IN  <<lo, lo + size>>

ChunkLo(w) == Chunk(N, W, w)[1]
ChunkHi(w) == Chunk(N, W, w)[2]

VARIABLES
    a0,             \* ghost: the input slice, a0[k] = <<key, k>>
    a,              \* the user's array (the slice)
    tmp,            \* scratch array (line 70)
    hist,           \* histograms : worker -> digit -> count  (line 71)
    offs,           \* offsets    : worker -> digit -> index  (line 72)
    varying, shift, bits, sourceIsA,
    fromA,          \* from_a captured by the closures of the current pass
    phase,          \* "hist" or "scatter": which f the current run executes
    mpc,            \* main program counter
    spawnNext,      \* run: next worker index to spawn
    firstUnstarted, \* run: workers firstUnstarted..W-1 were not spawned
    cw,             \* caller: argument of the f it currently executes
    cstage,         \* caller: "start" | "loop" | "idle"
    ci,             \* caller: loop index i
    cexc,           \* fixed run: caller holds a pending exception
    dstate,         \* domain d: "none" | "start" | "loop" | "finished"
    di,             \* domain d: loop index i
    ret,            \* "running" | "normal" | "raised"  (status of sort)
    exc,            \* ghost: "none" | "spawn" | "caller" (why sort raised)
    wcount          \* ghost: buffer -> index -> #writes in current run

vars == <<a0, a, tmp, hist, offs, varying, shift, bits, sourceIsA, fromA,
          phase, mpc, spawnNext, firstUnstarted, cw, cstage, ci, cexc,
          dstate, di, ret, exc, wcount>>

mainVars   == <<varying, shift, bits, sourceIsA, fromA, phase, mpc,
                spawnNext, firstUnstarted, cexc, ret, exc>>
callerVars == <<cw, cstage, ci>>
domVars    == <<dstate, di>>
dataVars   == <<a, tmp, hist, offs, wcount>>

Running(d) == dstate[d] \in {"start", "loop"}
ZeroTable  == [w \in WorkerIds |-> [d \in Digits |-> 0]]
NoWrites   == [b \in Bufs |-> [k \in Idx |-> 0]]

-----------------------------------------------------------------------------
(* Quantities of the current pass, as seen by the closures.                *)
Radix       == 2^bits                         \* line 77
Mask        == Radix - 1                      \* line 78
DigitOf(e)  == BitAnd(Lsr(Key(e), shift), Mask)   \* lines 88/94/104/112
Src         == IF fromA THEN a ELSE tmp
SrcName     == IF fromA THEN "a" ELSE "tmp"
DstName     == IF fromA THEN "tmp" ELSE "a"

(* First step of f w: histogram phase does Array.fill histogram 0 radix 0  *)
(* (line 83); the scatter phase only binds next / lo / hi (lines 99-100). *)
StartEffect(w) ==
    /\ IF phase = "hist"
         THEN hist' = [hist EXCEPT ![w] =
                         [d \in Digits |-> IF d < Radix THEN 0 ELSE hist[w][d]]]
         ELSE UNCHANGED hist
    /\ UNCHANGED <<a, tmp, offs, wcount>>

(* One iteration i of the loop of f w.                                     *)
IterEffect(w, i) ==
    LET e == Src[i]
        d == DigitOf(e)
    IN  IF phase = "hist"
          THEN \* lines 86-96
               /\ hist' = [hist EXCEPT ![w][d] = @ + 1]
               /\ UNCHANGED <<a, tmp, offs, wcount>>
          ELSE \* lines 101-116
               LET target == offs[w][d] IN
               /\ IF fromA
                    THEN tmp' = [tmp EXCEPT ![target] = e] /\ UNCHANGED a
                    ELSE a'   = [a   EXCEPT ![target] = e] /\ UNCHANGED tmp
               /\ offs'   = [offs EXCEPT ![w][d] = target + 1]
               /\ wcount' = [wcount EXCEPT ![DstName][target] = @ + 1]
               /\ UNCHANGED hist

(* Lines 47-54: prepare_offsets, executed sequentially by the caller.      *)
RECURSIVE PrepLoop(_, _, _, _, _)
PrepLoop(h, o, d, w, target) ==
    IF d > Radix - 1 THEN o
    ELSE IF w > W - 1 THEN PrepLoop(h, o, d + 1, 0, target)
    ELSE PrepLoop(h, [o EXCEPT ![w][d] = target], d, w + 1, target + h[w][d])

-----------------------------------------------------------------------------
Init ==
    /\ a0 \in {[k \in Idx |-> <<key[k], k>>] : key \in [Idx -> 0 .. MaxKey]}
    /\ a = a0
    /\ tmp = [k \in Idx |-> Zero]
    /\ hist = ZeroTable
    /\ offs = ZeroTable
    /\ varying = 0 /\ shift = 0 /\ bits = 0
    /\ sourceIsA = TRUE /\ fromA = TRUE /\ phase = "hist"
    /\ mpc = "init"
    /\ spawnNext = 1 /\ firstUnstarted = W
    /\ cw = 0 /\ cstage = "idle" /\ ci = 0 /\ cexc = FALSE
    /\ dstate = [d \in Domains |-> "none"]
    /\ di = [d \in Domains |-> 0]
    /\ ret = "running" /\ exc = "none"
    /\ wcount = NoWrites

(* Lines 64-74: compute varying; allocate tmp and the worker tables.       *)
Start ==
    /\ mpc = "init"
    /\ LET v == Varying(a) IN
         /\ varying' = v
         /\ IF v = 0
              THEN ret' = "normal" /\ mpc' = "returned"
              ELSE ret' = ret /\ mpc' = "loop"
    /\ UNCHANGED <<a0, dataVars, shift, bits, sourceIsA, fromA, phase,
                   spawnNext, firstUnstarted, cexc, exc, callerVars, domVars>>

(* Begin `run workers f` for f = the ph phase function.                    *)
BeginRun(ph) ==
    /\ phase' = ph
    /\ spawnNext' = 1
    /\ firstUnstarted' = W
    /\ cexc' = FALSE
    /\ cw' = 0 /\ cstage' = "start" /\ ci' = 0
    /\ wcount' = NoWrites
    /\ mpc' = IF W > 1 THEN "spawn" ELSE "f"

(* Lines 75-80, 119-121: the pass loop, pass skipping and the final blit. *)
MainLoop ==
    /\ mpc = "loop"
    /\ IF shift < KeyBits
         THEN LET bts == Min(DigitBits, KeyBits - shift) IN
              /\ bits' = bts
              /\ IF BitAnd(Lsr(varying, shift), 2^bts - 1) # 0
                   THEN /\ fromA' = sourceIsA
                        /\ BeginRun("hist")
                        /\ UNCHANGED <<shift>>
                   ELSE /\ shift' = shift + bts
                        /\ mpc' = "loop"
                        /\ UNCHANGED <<fromA, phase, spawnNext, firstUnstarted,
                                       cexc, callerVars, wcount>>
              /\ UNCHANGED <<a, ret>>
         ELSE /\ IF ~sourceIsA THEN a' = tmp ELSE UNCHANGED a   \* Array.blit
              /\ ret' = "normal"
              /\ mpc' = "returned"
              /\ UNCHANGED <<shift, bits, fromA, phase, spawnNext,
                             firstUnstarted, cexc, callerVars, wcount>>
    /\ UNCHANGED <<a0, tmp, hist, offs, varying, sourceIsA, exc, domVars>>

(* Line 97: prepare_offsets, then start the scatter run (line 98).         *)
Prepare ==
    /\ mpc = "prepare"
    /\ offs' = PrepLoop(hist, offs, 0, 0, 0)
    /\ BeginRun("scatter")
    /\ UNCHANGED <<a0, a, tmp, hist, varying, shift, bits, sourceIsA, fromA,
                   ret, exc, domVars>>

(* Line 39: Array.init (workers - 1) (fun i -> Domain.spawn ...).          *)
SpawnOk ==
    /\ mpc = "spawn"
    /\ dstate' = [dstate EXCEPT ![spawnNext] = "start"]
    /\ di' = [di EXCEPT ![spawnNext] = 0]
    /\ spawnNext' = spawnNext + 1
    /\ mpc' = IF spawnNext + 1 = W THEN "f" ELSE "spawn"
    /\ UNCHANGED <<a0, dataVars, varying, shift, bits, sourceIsA, fromA, phase,
                   firstUnstarted, cexc, ret, exc, callerVars>>

(* Domain.spawn raises Failure.                                            *)
(* original: the exception escapes Array.init, run and sort; the domains   *)
(*           already spawned are never joined.                             *)
(* fixed:    stop spawning; the caller will run f firstUnstarted..W-1.     *)
SpawnFail ==
    /\ SpawnCanFail
    /\ mpc = "spawn"
    /\ IF RunVariant = "original"
         THEN /\ ret' = "raised" /\ exc' = "spawn" /\ mpc' = "returned"
              /\ cstage' = "idle"
              /\ UNCHANGED firstUnstarted
         ELSE /\ firstUnstarted' = spawnNext
              /\ mpc' = "f"
              /\ UNCHANGED <<ret, exc, cstage>>
    /\ UNCHANGED <<a0, dataVars, varying, shift, bits, sourceIsA, fromA, phase,
                   spawnNext, cexc, cw, ci, domVars>>

(* The caller has returned from f cw.  original: line 42 (join).  fixed:   *)
(* run the chunks of the workers that could not be spawned, then join.    *)
CallerLeaveF ==
    LET nxt == IF cw = 0 THEN firstUnstarted ELSE cw + 1 IN
    IF nxt < W
      THEN cw' = nxt /\ cstage' = "start" /\ ci' = 0 /\ mpc' = "f"
      ELSE cw' = cw /\ cstage' = "idle" /\ ci' = 0 /\ mpc' = "join"

CallerStart ==
    /\ mpc = "f" /\ cstage = "start"
    /\ StartEffect(cw)
    /\ IF ChunkLo(cw) < ChunkHi(cw)
         THEN cstage' = "loop" /\ ci' = ChunkLo(cw) /\ UNCHANGED <<cw, mpc>>
         ELSE CallerLeaveF
    /\ UNCHANGED <<a0, varying, shift, bits, sourceIsA, fromA, phase, spawnNext,
                   firstUnstarted, cexc, ret, exc, domVars>>

CallerIter ==
    /\ mpc = "f" /\ cstage = "loop"
    /\ IterEffect(cw, ci)
    /\ IF ci + 1 < ChunkHi(cw)
         THEN ci' = ci + 1 /\ UNCHANGED <<cw, cstage, mpc>>
         ELSE CallerLeaveF
    /\ UNCHANGED <<a0, varying, shift, bits, sourceIsA, fromA, phase, spawnNext,
                   firstUnstarted, cexc, ret, exc, domVars>>

(* An asynchronous exception (e.g. Sys.Break) raised in the caller while   *)
(* it executes a worker function, before any of its steps.                 *)
(* original: it escapes run (joins skipped) and sort.                      *)
(* fixed:    remember it, join all spawned domains, then re-raise.         *)
CallerRaise ==
    /\ CallerCanRaise
    /\ mpc = "f" /\ cstage \in {"start", "loop"}
    /\ cstage' = "idle"
    /\ IF RunVariant = "original"
         THEN /\ ret' = "raised" /\ exc' = "caller" /\ mpc' = "returned"
              /\ UNCHANGED cexc
         ELSE /\ cexc' = TRUE /\ mpc' = "join"
              /\ UNCHANGED <<ret, exc>>
    /\ UNCHANGED <<a0, dataVars, varying, shift, bits, sourceIsA, fromA, phase,
                   spawnNext, firstUnstarted, cw, ci, domVars>>

(* Line 42: Array.iter Domain.join spawned.  Joining in order 1..W-1 is    *)
(* a sequence of blocking waits with no side effects, so it is one step    *)
(* enabled once every spawned domain has finished.                         *)
Join ==
    /\ mpc = "join"
    /\ \A d \in Domains : ~Running(d)
    /\ dstate' = [d \in Domains |-> "none"]
    /\ di' = [d \in Domains |-> 0]
    /\ IF cexc
         THEN \* fixed variant: re-raise after joining
              /\ ret' = "raised" /\ exc' = "caller" /\ mpc' = "returned"
              /\ UNCHANGED <<sourceIsA, shift>>
         ELSE IF phase = "hist"
         THEN /\ mpc' = "prepare"                        \* line 97
              /\ UNCHANGED <<ret, exc, sourceIsA, shift>>
         ELSE /\ sourceIsA' = ~sourceIsA                 \* line 117
              /\ shift' = shift + bits                   \* line 119
              /\ mpc' = "loop"
              /\ UNCHANGED <<ret, exc>>
    /\ UNCHANGED <<a0, dataVars, varying, bits, fromA, phase, spawnNext,
                   firstUnstarted, cexc, callerVars>>

(* Spawned domain d executing f d.                                         *)
DomainStart(d) ==
    /\ dstate[d] = "start"
    /\ StartEffect(d)
    /\ dstate' = [dstate EXCEPT ![d] =
                    IF ChunkLo(d) < ChunkHi(d) THEN "loop" ELSE "finished"]
    /\ di' = [di EXCEPT ![d] = ChunkLo(d)]
    /\ UNCHANGED <<a0, mainVars, callerVars>>

DomainIter(d) ==
    /\ dstate[d] = "loop"
    /\ IterEffect(d, di[d])
    /\ di' = [di EXCEPT ![d] = @ + 1]
    /\ dstate' = [dstate EXCEPT ![d] =
                    IF di[d] + 1 < ChunkHi(d) THEN "loop" ELSE "finished"]
    /\ UNCHANGED <<a0, mainVars, callerVars>>

(* sort has returned and every domain has stopped: nothing can happen.     *)
Terminated ==
    /\ ret # "running"
    /\ \A d \in Domains : ~Running(d)
    /\ UNCHANGED vars

Next ==
    \/ Start \/ MainLoop \/ Prepare \/ SpawnOk \/ SpawnFail \/ Join
    \/ CallerStart \/ CallerIter \/ CallerRaise
    \/ \E d \in Domains : DomainStart(d) \/ DomainIter(d)
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ a0 \in [Idx -> Elem] /\ a \in [Idx -> Elem] /\ tmp \in [Idx -> Elem]
    /\ hist \in [WorkerIds -> [Digits -> 0 .. N]]
    /\ offs \in [WorkerIds -> [Digits -> 0 .. N]]
    /\ varying \in 0 .. MaxKey
    /\ shift \in 0 .. KeyBits /\ bits \in 0 .. DigitBits
    /\ sourceIsA \in BOOLEAN /\ fromA \in BOOLEAN
    /\ phase \in {"hist", "scatter"}
    /\ mpc \in {"init", "loop", "spawn", "f", "join", "prepare", "returned"}
    /\ spawnNext \in 1 .. W /\ firstUnstarted \in 1 .. W
    /\ cw \in WorkerIds /\ cstage \in {"start", "loop", "idle"}
    /\ ci \in 0 .. N /\ cexc \in BOOLEAN
    /\ dstate \in [Domains -> {"none", "start", "loop", "finished"}]
    /\ di \in [Domains -> 0 .. N]
    /\ ret \in {"running", "normal", "raised"}
    /\ exc \in {"none", "spawn", "caller"}
    /\ wcount \in [Bufs -> [Idx -> Nat]]

(* Every index the next step of an active worker function will use is in   *)
(* bounds, i.e. no OCaml bounds check can fail.                            *)
ContextInBounds(w, stage, i) ==
    /\ w \in WorkerIds                                 \* histograms.(worker)
    /\ Radix <= MaxRadix                               \* Array.fill ... radix
    /\ 0 <= ChunkLo(w) /\ ChunkLo(w) <= ChunkHi(w) /\ ChunkHi(w) <= N
    /\ stage = "loop" =>
         /\ i \in Idx                                  \* a.(pos + i), tmp.(i)
         /\ DigitOf(Src[i]) \in Digits                 \* histogram.(d), next.(d)
         /\ phase = "scatter" => offs[w][DigitOf(Src[i])] \in Idx  \* dst.(target)

BoundsOK ==
    /\ mpc = "f" => ContextInBounds(cw, cstage, ci)
    /\ \A d \in Domains : Running(d) => ContextInBounds(d, dstate[d], di[d])
    /\ mpc = "prepare" => Radix <= MaxRadix            \* prepare_offsets

(* Race freedom inside a run.                                              *)
ScatterWritesDisjoint ==           \* no destination cell is written twice
    \A b \in Bufs, k \in Idx : wcount[b][k] <= 1
WritesOnlyToDestination ==         \* nobody writes the buffer being read
    \A b \in Bufs, k \in Idx :
        wcount[b][k] > 0 => (phase = "scatter" /\ b = DstName)
TablesPrivate ==                   \* no two running contexts share f w
    mpc = "f" => ~(cw \in Domains /\ Running(cw))
(* Every phase boundary is a join: no domain runs while the caller reads   *)
(* the histograms (prepare_offsets) or starts the next pass.               *)
NoDomainOutsideRun ==
    mpc \in {"init", "loop", "prepare"} => \A d \in Domains : dstate[d] = "none"

(* Functional correctness.                                                 *)
IsPerm(arr) == {arr[k] : k \in Idx} = {a0[k] : k \in Idx}
StablySorted(arr) ==
    \A k \in 0 .. N - 2 :
        \/ Key(arr[k]) < Key(arr[k + 1])
        \/ Key(arr[k]) = Key(arr[k + 1]) /\ Id(arr[k]) < Id(arr[k + 1])
CorrectOnNormalReturn ==
    ret = "normal" => IsPerm(a) /\ StablySorted(a)

(* Exception safety.                                                       *)
QuiescentOnReturn ==
    ret # "running" => \A d \in Domains : ~Running(d)
AllJoinedOnReturn ==
    ret # "running" => \A d \in Domains : dstate[d] = "none"
ContentsPreservedOnException ==
    ret = "raised" => IsPerm(a)
SpawnFailureIsBenign ==            \* spawn failure never makes sort raise
    exc # "spawn"
ReturnsNormally ==                 \* sort never raises
    ret # "raised"

NoMutationAfterReturn == [][ret # "running" => a' = a]_vars
Termination == <>(ret # "running")

=============================================================================
