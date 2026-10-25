module LinearModalLedger

(* Small executable F* model for fresh identities and modal admission.
   This proves properties of this mathematical model only; the GForth
   refinement/correspondence proof remains a separate obligation. *)

type mode =
  | Linear
  | Modal
  | Unknown

type ownership =
  | Live
  | Consumed

type kind =
  | Scalar
  | Closure
  | Result

type value = {
  id: nat;
  mode: mode;
  ownership: ownership;
  kind: kind
}

type state = {
  next_id: nat;
  values: list value
}

let rec has_id (id:nat) (values:list value) : prop =
  match values with
  | [] -> False
  | v::tail -> v.id = id \/ has_id id tail

let rec ids_below (bound:nat) (values:list value) : prop =
  match values with
  | [] -> True
  | v::tail -> v.id < bound /\ ids_below bound tail

let rec unique_ids (values:list value) : prop =
  match values with
  | [] -> True
  | v::tail -> not (has_id v.id tail) /\ unique_ids tail

let invariant (s:state) : prop =
  ids_below s.next_id s.values /\ unique_ids s.values

let rec lemma_absent_when_below (id:nat) (bound:nat) (values:list value)
  : Lemma
      (requires (id >= bound /\ ids_below bound values))
      (ensures (not (has_id id values)))
  =
  match values with
  | [] -> ()
  | v::tail ->
      assert (id <> v.id);
      lemma_absent_when_below id bound tail

let rec lemma_raise_bound (old_bound:nat) (new_bound:nat) (values:list value)
  : Lemma
      (requires (old_bound <= new_bound /\ ids_below old_bound values))
      (ensures (ids_below new_bound values))
  =
  match values with
  | [] -> ()
  | v::tail ->
      lemma_raise_bound old_bound new_bound tail

(* Allocation chooses next_id and proves that it cannot collide with any
   existing value identity, then monotonically increases next_id. *)
let add_fresh (s:state) (v:value{v.id = s.next_id})
  : Tot state
      (requires (invariant s))
      (ensures (fun s' ->
        invariant s' /\
        s'.next_id = s.next_id + 1 /\
        has_id v.id s'.values))
  =
  lemma_absent_when_below s.next_id s.next_id s.values;
  lemma_raise_bound s.next_id (s.next_id + 1) s.values;
  assert (not (has_id v.id s.values));
  assert (unique_ids (v::s.values));
  assert (ids_below (s.next_id + 1) (v::s.values));
  { next_id = s.next_id + 1; values = v::s.values }

type modal_decision =
  | AllowModal
  | RejectLinear
  | RejectUnknown
  | RejectConsumed

let modal_admission (v:value) : modal_decision =
  match v.ownership with
  | Consumed -> RejectConsumed
  | Live ->
      match v.mode with
      | Modal -> AllowModal
      | Linear -> RejectLinear
      | Unknown -> RejectUnknown

(* The checker proves that a linear value cannot be accepted for a modal
   operation, and a consumed value cannot be admitted regardless of mode. *)
let lemma_linear_rejected (v:value{v.mode = Linear}) :
  Lemma (modal_admission v = RejectLinear) = ()

let lemma_consumed_rejected (v:value{v.ownership = Consumed}) :
  Lemma (modal_admission v = RejectConsumed) = ()

let lemma_only_modal_is_admitted (v:value) :
  Lemma (requires (modal_admission v = AllowModal))
        (ensures (v.mode = Modal /\ v.ownership = Live)) = ()
