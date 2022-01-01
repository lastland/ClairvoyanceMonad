From Ltac2 Require Import Ltac2.

From Clairvoyance Require Import Core.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | false => b2
  | true => true
  end.

Definition orbA (b1 b2 : T bool) : M bool :=
  let! b1 := force b1 in
  match b1 with
  | false => force b2
  | true => ret true
  end.

Inductive optionA (a : Type) : Type :=
| SomeA : T a -> optionA a
| NoneA
.

Ltac2 option_get o :=
  match o with
  | Some x => x
  | None => Control.throw No_value
  end.

Ltac2 fresh x := Fresh.fresh (Fresh.Free.of_ids []) x.

Ltac2 mutable _compile_constructor (t : constr) := (None : constr option).

Ltac2 type_in_motive (t : constr) :=
  lazy_match! t with
  | (fun _ : ?u => _) => u
  end.

Ltac2 is_var (t : constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var _ => true
  | _ => false
  end.

Ltac2 Type exn ::= [ BadType (constr, constr) ].

Ltac2 rec _compile_type (t : constr) :=
  lazy_match! t with
  | bool => 'bool
  | option ?a => '(optionA ltac2:(refine (_compile_type a)))
  | (?a -> ?b) =>
    let a' := _compile_type a in
    let b' := _compile_type b in
    '(T $a' -> M $b')
  | ?u => if is_var u then u else Control.zero (BadType t t)
  end.

Ltac2 compile_type (t : constr) :=
  match Control.case (fun () => _compile_type t) with
  | Val ans => let (x, _) := ans in x
  | Err e => Control.throw
    (match e with
    | BadType _ u => BadType t u
    | e => Message.print (Message.of_string "Error in compile_type"); e
    end)
  end.

Ltac2 rec _compile (t : constr) :=
  match _compile_constructor t with Some t => t | None =>
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda b t =>
    let n :=
      match Constr.Binder.name b with
      | None => fresh @x
      | Some n => n
      end in
    let b' :=
      lazy_match! Constr.Binder.type b with
      | Type => 'Type
      | Set => 'Set
      | (Type -> Type) => '(Type -> Type)
      | (Set -> Set) => '(Set -> Set)
      | ?b => '(T ltac2:(refine (compile_type b)))
      end in
    Constr.in_context n b' (fun () =>
      refine (_compile (Constr.Unsafe.substnl [Control.hyp n] 0 t)))
  | Constr.Unsafe.Case info _motive _invert t0 ts =>
    let __case := fresh @__case in
    let tm := compile_type (type_in_motive _motive) in
    '(@Core.bind $tm _ ltac2:(refine (_compile t0)) ltac2:(refine
       (Constr.in_context __case tm (fun () =>
         refine (Constr.Unsafe.make (Constr.Unsafe.Case info '(fun _ => _) _invert (Control.hyp __case) (Array.map _compile ts)))))))
  | Constr.Unsafe.Var v =>
    let v := Control.hyp v in
    '(Clairvoyance.Core.force $v)
  | Constr.Unsafe.Constructor _ _ => '(Core.ret $t)
  | _ => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "WOOPS! ") (Message.of_constr t))))
  end end.

Ltac2 Set _compile_constructor := fun (t : constr) =>
  lazy_match! t with
  | @Some _ ?x =>
    let __x := fresh @__x in
    Some '(@Core.bind _ _ (Core.thunk ltac2:(refine (_compile x))) ltac2:(refine
       (Constr.in_context __x '_ (fun () => ()))))
  | None => Some '(Core.ret None)
  | _ => None
  end.

Ltac2 compile (t : constr) :=
  let t := Std.eval_red t in
  Control.enter (fun () => refine (_compile t)).

Definition orbA_ := ltac2:(compile 'orb).
Fail Definition option_mapA_ := ltac2:(compile ' option_map).
