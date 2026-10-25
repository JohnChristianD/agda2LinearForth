module LinearModalABI

(* F*-style specification interface for the checked Agda-to-Gforth runtime.
   This file is not yet machine-checked, has no concrete model implementation,
   and does not prove that data/FLib.fth refines these contracts. *)

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

(* Model predicates. The forthcoming concrete model must define these and
   prove invariant preservation rather than assume them as axioms. *)
val invariant : state -> Tot prop
val live : state -> handle -> Tot prop
val consumed : state -> handle -> Tot prop
val has_mode : state -> handle -> mode -> Tot prop
val mode_of : state -> handle -> Tot (option mode)
val has_kind : state -> handle -> value_kind -> Tot prop
val resource_of : state -> handle -> Tot (option resource_id)
val owns_resource : state -> handle -> resource_id -> Tot prop
val contained_by : state -> resource_id -> handle -> Tot prop
val fresh_handle : state -> handle -> Tot prop
val linear_safe : state -> handle -> Tot prop
val modal_safe : state -> handle -> Tot prop
val all_captures_modal : state -> handle -> Tot prop
val payload_mode_valid : state -> handle -> mode -> Tot prop
val accepts_argument : state -> handle -> mode -> Tot prop
val transfer_complete : state -> state -> handle -> handle -> Tot prop
val same_state : state -> state -> Tot prop
val all_resources_accounted : state -> Tot prop
val promotable : state -> handle -> Tot prop
val valid_import : state -> nat -> value_kind -> mode -> Tot prop
val mode_evidence : state -> nat -> mode -> Tot prop
val payload_of : state -> handle -> Tot (option handle)
val abi_checked : state -> Tot prop
val primitive_contract : state -> handle -> Tot prop
val force_failure_valid : state -> state -> handle -> Tot prop
val result_transition_valid : state -> state -> handle -> handle -> mode -> Tot prop

(* Import is the only admission path for legacy/unmanaged representations.
   valid_import must validate the representation and justify the supplied
   mode. No numeric threshold may decide whether a cell is an object. *)
val abi_import :
  s:state -> raw_cell:nat -> k:value_kind -> m:mode ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s /\ valid_import s raw_cell k m))
    (ensures (fun out ->
      match out with
      | Success s' h ->
          invariant s' /\ all_resources_accounted s' &&
          live s' h /\ fresh_handle s' h &&
          has_kind s' h k /\ has_mode s' h m &&
          payload_mode_valid s' h m
      | Failure s' _ -> invariant s' /\ same_state s s'))

(* The mode must be backed by compiler/loader evidence. This operation
   makes a tracked scalar handle; it does not infer a mode from the raw cell. *)
val abi_make_scalar :
  s:state -> raw_value:nat -> m:mode ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s /\ mode_evidence s raw_value m))
    (ensures (fun out ->
      match out with
      | Success s' h ->
          invariant s' /\ all_resources_accounted s' /\
          live s' h /\ fresh_handle s' h /\
          has_kind s' h Scalar /\ has_mode s' h m /\
          payload_mode_valid s' h m
      | Failure s' _ -> invariant s' /\ same_state s s'))

(* PASS partially applies a closure and returns a fresh closure. It consumes
   the function token only if that function is linear. It moves a linear
   argument into the new environment (consuming the old token), but retains
   a modal argument as a modal shared value. The returned closure is linear
   if either input is linear; otherwise it is modal. This is specifically the
   partial-application contract; executing the closure is specified by force. *)
val abi_pass :
  s:state -> fn:handle -> arg:handle ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s &&
      live s fn /\ has_kind s fn Closure &&
      (mode_of s fn = Some Linear \/ mode_of s fn = Some Modal) &&
      live s arg &&
      (mode_of s arg = Some Linear \/ mode_of s arg = Some Modal) &&
      accepts_argument s fn (match mode_of s arg with
        | Some m -> m
        | None -> Linear)))
    (ensures (fun out ->
      match out with
      | Success s' result ->
          invariant s' /\ all_resources_accounted s' &&
          fresh_handle s' result /\ live s' result &&
          has_kind s' result Closure &&
          ((mode_of s fn = Some Linear) ==> consumed s' fn) &&
          ((mode_of s fn = Some Modal) ==> live s' fn) &&
          ((mode_of s arg = Some Linear) ==>
            (consumed s' arg /\ transfer_complete s s' arg result)) &&
          ((mode_of s arg = Some Modal) ==> live s' arg) &&
          ((mode_of s fn = Some Linear \/ mode_of s arg = Some Linear) ==>
            has_mode s' result Linear) &&
          ((mode_of s fn = Some Modal /\ mode_of s arg = Some Modal) ==>
            (has_mode s' result Modal /\ modal_safe s' result))
      | Failure s' _ -> invariant s' /\ same_state s s'))

(* Promotion does not infer modal safety from a wrapper bit. The predicate
   promotable summarizes proved/trusted code, payload, effect, and environment
   premises; all_captures_modal is independently required. *)
val abi_promote_modal :
  s:state -> h:handle ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s /\ live s h &&
      has_kind s h Closure /\ promotable s h /\ all_captures_modal s h))
    (ensures (fun out ->
      match out with
      | Success s' h' ->
          invariant s' /\ all_resources_accounted s' &&
          live s' h' /\ has_mode s' h' Modal &&
          modal_safe s' h' /\ all_captures_modal s' h'
      | Failure s' _ -> invariant s' /\ same_state s s'))

val abi_dup_modal :
  s:state -> h:handle ->
  Tot (outcome (handle & handle))
    (requires (invariant s /\ abi_checked s /\ live s h &&
      has_mode s h Modal /\ modal_safe s h &&
      payload_mode_valid s h Modal))
    (ensures (fun out ->
      match out with
      | Success s' pair ->
          let (h1, h2) = pair in
          invariant s' /\ all_resources_accounted s' &&
          live s' h1 /\ live s' h2 &&
          has_mode s' h1 Modal /\ has_mode s' h2 Modal &&
          modal_safe s' h1 /\ modal_safe s' h2
      | Failure s' _ -> invariant s' /\ same_state s s'))

val abi_drop_modal :
  s:state -> h:handle ->
  Tot (outcome unit)
    (requires (invariant s /\ abi_checked s /\ live s h &&
      has_mode s h Modal /\ modal_safe s h))
    (ensures (fun out ->
      match out with
      | Success s' _ -> invariant s' /\ all_resources_accounted s' /\ consumed s' h
      | Failure s' _ -> invariant s' /\ same_state s s'))

(* Forcing may execute code with effects, so a failed force need not restore
   the original state. force_failure_valid must instead prove that every
   resource remains accounted for, no consumed token is resurrected, and the
   returned exception outcome owns any in-flight resources. *)
val abi_force :
  s:state -> h:handle ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s /\ live s h &&
      has_kind s h Closure /\ all_resources_accounted s))
    (ensures (fun out ->
      match out with
      | Success s' result ->
          invariant s' /\ all_resources_accounted s' &&
          live s' result /\ all_resources_accounted s'
      | Failure s' _ ->
          invariant s' /\ all_resources_accounted s' &&
          force_failure_valid s s' h))

(* Wrapping transfers a linear payload into a fresh result token; it must not
   alias the payload's linear ownership. Modal payloads may be shared only
   under the modal-safety contract. The mode is preserved, never strengthened. *)
val abi_make_result :
  s:state -> payload:handle -> m:mode ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s /\ live s payload &&
      has_mode s payload m /\ payload_mode_valid s payload m))
    (ensures (fun out ->
      match out with
      | Success s' r ->
          invariant s' /\ all_resources_accounted s' &&
          live s' r /\ fresh_handle s' r /\ has_kind s' r Result &&
          has_mode s' r m /\ payload_mode_valid s' r m &&
          result_transition_valid s s' payload r m
      | Failure s' _ -> invariant s' /\ same_state s s'))

(* This contract specifically rules out tagging a RESULT as Modal when its
   contained payload is linear, unknown, or otherwise not modal-safe. *)
val abi_assert_modal_value :
  s:state -> wrapper:handle ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s /\ live s wrapper /\
      has_kind s wrapper Result /\
      (match payload_of s wrapper with
       | Some payload -> live s payload /\ has_mode s payload Modal /\
           payload_mode_valid s payload Modal
       | None -> False)))
    (ensures (fun out ->
      match out with
      | Success s' h ->
          invariant s' /\ all_resources_accounted s' /\
          live s' h /\ has_mode s' h Modal /\ modal_safe s' h
      | Failure s' _ -> invariant s' /\ same_state s s'))

(* Only primitives with complete reviewed contracts are callable by checked
   code. An unlisted Forth word is rejected before generated code is admitted. *)
val abi_call_primitive :
  s:state -> primitive:handle -> args:list handle ->
  Tot (outcome handle)
    (requires (invariant s /\ abi_checked s /\ primitive_contract s primitive &&
      all_resources_accounted s))
    (ensures (fun out ->
      match out with
      | Success s' result ->
          invariant s' /\ all_resources_accounted s' /\ live s' result
      | Failure s' _ -> invariant s' /\ all_resources_accounted s'))
