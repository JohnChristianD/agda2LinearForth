module LinearModalABI

(* Specification interface for the Agda-to-Gforth checked runtime.
   This file is an F*-style contract artifact, not yet machine-checked and
   not a proof that data/FLib.fth refines these contracts. *)

type handle = nat
type resource_id = nat
type state

type mode =
  | Linear
  | Modal

type value_kind =
  | Scalar
  | Constructor
  | Closure
  | Result

type abi_error =
  | UnknownHandle
  | ConsumedHandle
  | ModeMismatch
  | UnsafeClosure
  | UnsafePayload
  | InvalidRepresentation
  | LinearResourceLost
  | AliasedLinearResource
  | UnsupportedPrimitive
  | AbiVersionMismatch

type outcome (a:Type) =
  | Success : state -> a -> outcome a
  | Failure : state -> abi_error -> outcome a

(* Abstract predicates are model vocabulary. A proof implementation must
   define them over a concrete state and discharge each transition contract. *)
val invariant : state -> Tot prop
val live : state -> handle -> Tot prop
val consumed : state -> handle -> Tot prop
val has_mode : state -> handle -> mode -> Tot prop
val has_kind : state -> handle -> value_kind -> Tot prop
val resource_of : state -> handle -> option resource_id -> Tot prop
val owns_resource : state -> handle -> resource_id -> Tot prop
val contained_by : state -> resource_id -> handle -> Tot prop
val fresh_handle : state -> handle -> Tot prop
val linear_safe : state -> handle -> Tot prop
val modal_safe : state -> handle -> Tot prop
val all_captures_modal : state -> handle -> Tot prop
val payload_mode_valid : state -> handle -> mode -> Tot prop
val accepts_argument : state -> handle -> mode -> Tot prop
val transfer_complete : state -> state -> handle -> handle -> Tot prop
val all_resources_accounted : state -> handle -> Tot prop
val promotable : state -> handle -> Tot prop
val abi_checked : state -> Tot prop
val primitive_contract : state -> handle -> Tot prop

(* Import is the only admission path for legacy/unmanaged representations.
   It must validate representation and supply a justified mode; it cannot use
   a MAXNUM-like numeric threshold. *)
val abi_import :
  s:state -> raw_cell:nat -> k:value_kind -> m:mode ->
  Tot (outcome handle)
    (requires (invariant s && abi_checked s))
    (ensures (fun out ->
      match out with
      | Success s' h ->
          invariant s' && live s' h && fresh_handle s' h &&
          has_kind s' h k && has_mode s' h m && payload_mode_valid s' h m
      | Failure s' _ -> invariant s'))

(* A linear capture moves the resource to the new closure. Old public tokens
   become consumed; resource identity survives inside the new environment. *)
val abi_pass_linear :
  s:state -> fn:handle -> arg:handle ->
  Tot (outcome handle)
    (requires (invariant s && abi_checked s &&
      live s fn && has_kind s fn Closure && accepts_argument s fn Linear &&
      linear_safe s fn && live s arg && has_mode s arg Linear && fn <> arg))
    (ensures (fun out ->
      match out with
      | Success s' h ->
          invariant s' && consumed s' fn && consumed s' arg &&
          live s' h && fresh_handle s' h && has_kind s' h Closure &&
          has_mode s' h Linear && transfer_complete s s' arg h &&
          all_resources_accounted s' h
      | Failure s' _ -> invariant s' && live s fn && live s' arg))

val abi_pass_modal :
  s:state -> fn:handle -> arg:handle ->
  Tot (outcome handle)
    (requires (invariant s && abi_checked s &&
      live s fn && has_kind s fn Closure && accepts_argument s fn Modal &&
      live s arg && has_mode s arg Modal && modal_safe s arg))
    (ensures (fun out ->
      match out with
      | Success s' h ->
          invariant s' && consumed s' fn && live s' h &&
          fresh_handle s' h && has_kind s' h Closure &&
          all_resources_accounted s' h
      | Failure s' _ -> invariant s' && live s fn && live s' arg))

(* Promotion may not infer modal safety from a wrapper bit. All code,
   environment, payload and effect premises are summarized by promotable. *)
val abi_promote_modal :
  s:state -> h:handle ->
  Tot (outcome handle)
    (requires (invariant s && abi_checked s && live s h &&
      has_kind s h Closure && promotable s h &&
      all_captures_modal s h))
    (ensures (fun out ->
      match out with
      | Success s' h' ->
          invariant s' && live s' h' && has_mode s' h' Modal &&
          modal_safe s' h' && all_captures_modal s' h'
      | Failure s' _ -> invariant s' && live s h))

val abi_dup_modal :
  s:state -> h:handle ->
  Tot (outcome (handle & handle))
    (requires (invariant s && abi_checked s && live s h &&
      has_mode s h Modal && modal_safe s h && payload_mode_valid s h Modal))
    (ensures (fun out ->
      match out with
      | Success s' (h1, h2) ->
          invariant s' && live s' h1 && live s' h2 &&
          has_mode s' h1 Modal && has_mode s' h2 Modal &&
          modal_safe s' h1 && modal_safe s' h2
      | Failure s' _ -> invariant s'))

val abi_drop_modal :
  s:state -> h:handle ->
  Tot (outcome unit)
    (requires (invariant s && abi_checked s && live s h &&
      has_mode s h Modal && modal_safe s h))
    (ensures (fun out ->
      match out with
      | Success s' _ -> invariant s' && consumed s' h
      | Failure s' _ -> invariant s'))

(* Force must account for every captured linear resource. Failure may not
   strand ownership in an unspecified state or resurrect a consumed handle. *)
val abi_force :
  s:state -> h:handle ->
  Tot (outcome handle)
    (requires (invariant s && abi_checked s && live s h &&
      has_kind s h Closure && all_resources_accounted s h))
    (ensures (fun out ->
      match out with
      | Success s' result ->
          invariant s' && live s' result && all_resources_accounted s' result
      | Failure s' _ -> invariant s' && all_resources_accounted s' h))

(* Result wrapping must preserve, not strengthen, the payload's mode. *)
val abi_make_result :
  s:state -> payload:handle -> m:mode ->
  Tot (outcome handle)
    (requires (invariant s && abi_checked s && live s payload &&
      has_mode s payload m && payload_mode_valid s payload m))
    (ensures (fun out ->
      match out with
      | Success s' r ->
          invariant s' && live s' r && has_kind s' r Result &&
          has_mode s' r m && payload_mode_valid s' r m
      | Failure s' _ -> invariant s' && live s' payload))

(* Only primitives with a complete reviewed contract are callable in the
   checked subset. Unlisted Forth words are rejected during code generation. *)
val abi_call_primitive :
  s:state -> primitive:handle -> args:list handle ->
  Tot (outcome handle)
    (requires (invariant s && abi_checked s && primitive_contract s primitive))
    (ensures (fun out ->
      match out with
      | Success s' result ->
          invariant s' && live s' result && all_resources_accounted s' result
      | Failure s' _ -> invariant s'))
