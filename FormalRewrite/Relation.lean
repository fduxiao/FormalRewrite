import FormalRewrite.Axioms

/-!
# Relations

A relation is just a binary predicate over some type
-/

abbrev Relation (A: Type) := A -> A -> Prop

class Reflexive (P: Relation A) where
  refl: forall {a: A}, P a a

def Relation.refl {A: Type} {P: Relation A} [inst: Reflexive P]:
  forall {a: A}, P a a := inst.refl


class Antisymmetric (P: Relation A) where
  anti: forall {a b: A}, P a b -> P b a -> a = b

def Relation.anti {A: Type} {P: Relation A} [inst: Antisymmetric P]:
  forall {a b: A}, P a b -> P b a -> a = b := inst.anti


class Transitive (P: Relation A) where
  trans: forall {a b c: A}, P a b -> P b c -> P a c

def Relation.trans {A: Type} {P: Relation A} [inst: Transitive P]:
  forall {a b c: A}, P a b -> P b c -> P a c := inst.trans


class Symmetric (P: Relation A) where
  symm: forall {a b: A}, P a b -> P b a

def Relation.symm {A: Type} {P: Relation A} [inst: Symmetric P]:
  forall {a b: A}, P a b -> P b a := inst.symm


inductive Fold (P: Relation A): Nat -> Relation A where
  | zero: Fold P 0 a a
  | succ: Fold P n a b -> P b c -> Fold P (n+1) a c


inductive Inverse (P: Relation A): Relation A where
  | inv: P a b -> Inverse P b a


def Relation.inv (P: Relation A): P a b -> Inverse P b a:= Inverse.inv


/--
The defintion of a sub relation
-/
class SubRel (P: Relation A) (Q: Relation A): Prop where
  inclusion: forall {a b: A}, P a b -> Q a b

notation: 60 P " sub_rel " Q => SubRel P Q

def Relation.inclusion {A: Type} {P: Relation A} {Super: Relation A}
  [inst: P sub_rel Super]: forall {a b: A}, P a b -> Super a b :=
    inst.inclusion

/-!
`SubRel` is it self a poset on all relations
-/
section

instance sub_rel_refl: P sub_rel P where
  inclusion := id

instance: forall {A: Type}, Reflexive (SubRel (A := A)) where
  refl := by
    intros P
    apply sub_rel_refl


instance: forall {A: Type}, Transitive (SubRel (A := A)) where
  trans {P Q R} {s1 s2} := by
    apply SubRel.mk
    intros a b H
    apply Q.inclusion
    apply P.inclusion
    apply H


theorem sub_rel_equiv: forall {A: Type} {P Q: Relation A},
  (P sub_rel Q) -> (Q sub_rel P) -> forall {a b: A}, P a b <-> Q a b := by
  intros A P Q s1 s2
  intros a b
  constructor
  . apply s1.inclusion
  . apply s2.inclusion

theorem rel_eq: forall {A: Type} {P Q: Relation A}, (forall x y: A, P x y <-> Q x y) -> P = Q := by
  intros A P Q H
  apply funext
  intros x
  apply funext
  intros y
  apply propext
  apply H

instance: forall {A: Type}, Antisymmetric (SubRel (A := A)) where
  anti := by
    intros P Q s1 s2
    apply rel_eq
    intros a b
    apply Iff.intro
    . apply s1.inclusion
    . apply s2.inclusion

end


/-!
The next thing is to prove what is a closure.
-/
section Closure

abbrev RelationOp (A: Type) := Relation A -> Relation A
abbrev RelationPred (A: Type) := Relation A -> Prop

/-!
The closure fo each type is clear.
-/
class Closure {A: Type} (Pred: outParam (RelationPred A)) (P: outParam (Relation A)) (C: Relation A) where
  inclusion: P sub_rel C
  pred: Pred C
  least: forall {Q: Relation A}, Pred Q -> (P sub_rel Q) -> C sub_rel Q


/-!
We instantly have the following.
-/
instance {A: Type} {P C: Relation A} {Pred: RelationPred A} [inst: Closure Pred P C]:
  P sub_rel C := inst.inclusion

instance cl_cl_sub {A: Type} {Pred: RelationPred A} {P: Relation A} {C1 C2: Relation A}
  [inst1: Closure Pred P C1] [inst2: Closure Pred P C2]: C1 sub_rel C2 where
    inclusion := by
      intros a b
      let sub := @inst1.least C2 inst2.pred inst2.inclusion
      apply sub.inclusion


theorem cl_unique: forall {A: Type} {Pred: RelationPred A} {P: Relation A} {C1 C2: Relation A}
  [Closure Pred P C1] [Closure Pred P C2], C1 = C2 := by
  intros A Pred P C1 C2 inst1 inst2
  apply rel_eq
  apply sub_rel_equiv
  . /- C1 sub_rel C2 -/
    apply @cl_cl_sub A Pred P C1 C2 inst1 inst2
  . /- C2 sub_rel C1 -/
    apply @cl_cl_sub A Pred P C2 C1 inst2 inst1

/-!
We can also define a closure operator.
-/
class ClosureOp {A: Type} (Pred: outParam (RelationPred A)) (Cl: outParam (RelationOp A)) where
  close (P: Relation A): Closure Pred P (Cl P)
  closed {P: Relation A} := close P
  inclusion {P: Relation A} := closed.inclusion (P := P)
  pred {P: Relation A} := closed.pred (P := P)
  least {P Q: Relation A} := closed.least (P := P) (Q := Q)


def RelationOp.close {A: Type} (Cl: RelationOp A) (P: Relation A) {Pred: RelationPred A}
  [inst: ClosureOp Pred Cl] := inst.close P

def RelationOp.closed {A: Type} (Cl: RelationOp A) {P: Relation A} {Pred: RelationPred A}
  [inst: ClosureOp Pred Cl] := inst.close P

/-!
Then, the `Closure` instances are defined as follows.
-/
instance {A: Type} {Pred: RelationPred A} (Cl: RelationOp A) [inst: ClosureOp Pred Cl]
  (P: Relation A): Closure Pred P (Cl P) := inst.closed


instance {A: Type} {Pred: RelationPred A} {Cl: RelationOp A} [inst: ClosureOp Pred Cl] {P: Relation A}:
  P sub_rel (Cl P) := (inst.closed).inclusion

instance cl_op_cl_op_sub {A: Type} {Pred: RelationPred A} {C1 C2: RelationOp A}
  [inst1: ClosureOp Pred C1] [inst2: ClosureOp Pred C2] {P: Relation A}: C1 P sub_rel C2 P where
    inclusion := by
      intros a b
      let sub := @inst1.least P (C2 P) inst2.pred inst2.inclusion
      apply sub.inclusion

instance cl_mono {A: Type} {Pred: RelationPred A} {Cl: RelationOp A} [inst: ClosureOp Pred Cl]
  {P Q: Relation A} [r1: P sub_rel Q]: Cl P sub_rel Cl Q where
  inclusion := by
    have r2: Q sub_rel Cl Q := inst.inclusion
    have r3: P sub_rel Cl Q := Relation.trans r1 r2
    let H := @inst.least P (Cl Q) inst.pred r3
    intros a b
    apply H.inclusion

theorem rel_op_eq: forall {A: Type} {C1 C2: RelationOp A},
  (forall {P: Relation A}, C1 P = C2 P) -> C1 = C2 := by
  intros A C1 C2 H
  apply funext
  apply H

theorem cl_op_unique: forall {A: Type} {Pred: RelationPred A} (C1 C2: RelationOp A),
  [ClosureOp Pred C1] -> [ClosureOp Pred C2] -> C1 = C2 := by
  intros A pred C1 C2 inst1 inst2
  apply rel_op_eq
  intros P
  apply rel_eq
  apply sub_rel_equiv
  . apply @cl_op_cl_op_sub A pred C1 C2 inst1 inst2
  . apply @cl_op_cl_op_sub A pred C2 C1 inst2 inst1

/-!
Then, it is reasonable to define the following.
-/

def Relation.closed {A: Type} {Pred: RelationPred A} {Cl: RelationOp A} [inst: ClosureOp Pred Cl]
  {P: Relation A} := inst.close P

def Relation.pred {A: Type} {Pred: RelationPred A} {Cl: RelationOp A} [inst: ClosureOp Pred Cl]
  {P: Relation A}: Pred (Cl P) := inst.pred

def Relation.least {A: Type} {Pred: RelationPred A} (Cl: RelationOp A) [inst: ClosureOp Pred Cl]
  {P: Relation A}: forall {Q: Relation A}, Pred Q -> (P sub_rel Q) -> (Cl P sub_rel Q) := inst.least


/-!
We are going to deal with a closure `Cl` with respect to `Pred`
-/
variable {A: Type}
variable {P: Relation A}
variable {Pred: RelationPred A}
variable {Cl: RelationOp A}
variable [inst: ClosureOp Pred Cl]

instance cl_cl_sub_cl: Cl (Cl P) sub_rel (Cl P) := inst.least (P := Cl P) (Q := Cl P) inst.pred Relation.refl

theorem cl_cl_is_cl {Cl: RelationOp A} [inst: ClosureOp Pred Cl]: Cl (Cl P) = Cl P := by
  apply rel_eq
  apply sub_rel_equiv
  . apply cl_cl_sub_cl
  . apply @inst.inclusion
end Closure


/---
Reflexive closure
-/
inductive RCl (P: Relation A): Relation A where
  | inclusion: P a b -> RCl P a b
  | refl: RCl P a a

instance RCl.close {A: Type} (P: Relation A): Closure Reflexive P (RCl P) where
  inclusion := SubRel.mk RCl.inclusion
  pred := Reflexive.mk RCl.refl
  least := by
    intros Q inst sub
    apply SubRel.mk
    intros a b H
    cases H
    case inclusion Hab =>
      apply P.inclusion
      apply Hab
    case refl => apply inst.refl


instance {A: Type}: ClosureOp Reflexive (RCl (A := A)) where
  close := RCl.close

instance: Reflexive (RCl P) where
  refl := RCl.refl


theorem rcl_ab_or_eq {A: Type} {P: Relation A}:
  forall {a b: A}, RCl P a b -> P a b ∨ a = b := by
  intros a b H
  induction H
  case inclusion a b Hab =>
    left
    apply Hab
  case refl a =>
    right
    rfl


/--
Transitive closure
-/
inductive TCl (P: Relation A): Relation A where
  | inclusion: P a b -> TCl P a b
  | trans: TCl P a b -> TCl P b c -> TCl P a c

instance TCl.close {A: Type} (P: Relation A): Closure Transitive P (TCl P) where
  inclusion := SubRel.mk TCl.inclusion
  pred := Transitive.mk TCl.trans
  least := by
    intros Q sub inst
    apply SubRel.mk
    intros a b H
    induction H
    case inclusion Hab =>
      apply P.inclusion
      apply Hab
    case trans Hab Hbc =>
      apply Q.trans
      apply Hab
      apply Hbc


instance {A: Type}: ClosureOp Transitive (TCl (A := A)) where
  close := TCl.close


instance: Transitive (TCl P) where
  trans := TCl.trans


instance [Reflexive P]: Reflexive (TCl P) where
  refl {a} := by
    apply TCl.inclusion
    apply P.refl

instance [Transitive P]: Transitive (RCl P) where
  trans {a b c} H1 H2 := by
    cases H1
    case inclusion Hab =>
      cases H2
      case inclusion Hbc =>
        apply P.inclusion
        apply P.trans Hab Hbc
      case refl =>
        apply RCl.inclusion
        apply Hab
    case refl =>
      apply H2


/--
`Reflexive` and `Transitive` predicate
-/
def RTPred {A: Type}: RelationPred A := fun (P: Relation A) => Reflexive P ∧ Transitive P

/--
`Reflexive` and `Transitive` Closure
-/
inductive RTCl (P: Relation A): Relation A where
  | inclusion: P a b -> RTCl P a b
  | refl: RTCl P a a
  | trans: RTCl P a b -> RTCl P b c -> RTCl P a c


instance RTCl.close (P: Relation A): Closure RTPred P (RTCl P) where
  inclusion := SubRel.mk RTCl.inclusion
  pred := by
    constructor
    . apply Reflexive.mk
      apply RTCl.refl
    . apply Transitive.mk
      apply RTCl.trans
  least := by
    intros Q inst sub
    let inst_refl := inst.left
    let inst_trans := inst.right
    apply SubRel.mk
    intros a b H
    induction H
    case inclusion Hab => apply P.inclusion Hab
    case refl => apply Q.refl
    case trans Hab Hbc => apply Q.trans Hab Hbc


instance rt_cl_op {A: Type}: ClosureOp RTPred (RTCl (A := A)) where
  close := RTCl.close


instance: Reflexive (RTCl P) where
  refl := RTCl.refl

instance: Transitive (RTCl P) where
  trans := RTCl.trans


/-!
Then we prove the equivalence between RTCl P, RCl (TCl P) and TCl (RCl P)
-/
abbrev RTCl2 (P: Relation A) := RCl (TCl P)

instance RTCl2.close (P: Relation A): Closure RTPred P (RTCl2 P) where
  inclusion := by
    apply SubRel.mk
    intros a b H
    apply (TCl P).inclusion
    apply P.inclusion
    apply H
  pred := by
    constructor
    . /- Reflexive -/
      apply Reflexive.mk
      intros a
      apply Relation.refl
    . /- Transitive -/
      apply Transitive.mk
      intros a b c
      apply Relation.trans
  least := by
    intros Q inst sub
    let inst_refl := inst.left
    let inst_trans := inst.right
    apply (RCl.close (TCl P)).least inst_refl
    apply (TCl.close P).least inst_trans
    exact sub


instance rt2_cl_op {A: Type}: ClosureOp RTPred (RTCl2 (A := A)) where
  close := RTCl2.close

theorem rt2_eq_rt: @RTCl2 = @RTCl := by
  apply funext
  intros A
  let H := @cl_op_unique A RTPred RTCl2 RTCl rt2_cl_op rt_cl_op
  apply H


abbrev RTCl3 (P: Relation A) := TCl (RCl P)

instance RTCl3.close (P: Relation A): Closure RTPred P (RTCl3 P) where
  inclusion := by
    apply SubRel.mk
    intros a b H
    apply (TCl P).inclusion
    apply P.inclusion
    apply H
  pred := by
    constructor
    . /- Reflexive -/
      apply Reflexive.mk
      intros a
      apply (TCl (RCl P)).refl
    . /- Transitive -/
      apply Transitive.mk
      intros a b c
      apply (TCl (RCl P)).trans
  least := by
    intros Q inst sub
    let inst_refl := inst.left
    let inst_trans := inst.right
    apply (TCl.close (RCl P)).least inst_trans
    apply (RCl.close P).least inst_refl
    exact sub


instance rt3_cl_op {A: Type}: ClosureOp RTPred (RTCl3 (A := A)) where
  close := RTCl3.close

theorem rt3_eq_rt: @RTCl3 = @RTCl := by
  apply funext
  intros A
  let H := @cl_op_unique A RTPred RTCl3 RTCl rt3_cl_op rt_cl_op
  apply H


/--
Symmetric closure
-/
inductive SCl (P: Relation A): Relation A where
  | inclusion: P a b -> SCl P a b
  | symm: SCl P a b -> SCl P b a

instance: P sub_rel SCl P where
  inclusion := SCl.inclusion

instance: Symmetric (SCl P) where
  symm := SCl.symm

instance [P sub_rel R] [Symmetric R]: SCl P sub_rel R where
  inclusion {a b} H := by
    induction H
    case inclusion Hab =>
      apply P.inclusion
      apply Hab
    case symm Hab =>
      apply R.symm
      apply Hab

theorem scl_ab_or_ba {A} {P: Relation A}: forall {a b: A}, SCl P a b -> P a b ∨ P b a := by
  intros a b H
  induction H
  case inclusion a b Hab =>
    left; apply Hab
  case symm a b H IHH =>
    cases IHH
    case inl Hab =>
      right; apply Hab
    case inr Hba =>
      left; apply Hba


instance [Reflexive P]: Reflexive (SCl P) where
  refl {a}:= by
    apply SCl.inclusion
    apply P.refl

instance [Symmetric P]: Symmetric (RCl P) where
  symm {a b} H := by
    cases H
    case inclusion Hab =>
      apply P.inclusion
      apply P.symm Hab
    case refl Hab =>
      apply (RCl P).refl

instance [Symmetric P]: Symmetric (TCl P) where
  symm {a b} H := by
    induction H
    case inclusion Hab =>
      apply P.inclusion
      apply P.symm Hab
    case trans a b c _ _ Hba Hcb =>
      apply (TCl P).trans Hcb Hba

/-!
The symmetric closure of a transitive relation is not transitive
Think about a set ${a, b, c}$, and relation ${(a, b), (c, b)}$, which is transitive.
Then, the symmetric closure is ${(a, b), (b, a), (c, b), (b, c)}$.
We can find $(a, b)$ and $(b, c)$ in that, but not $(a, c)$.
-/
namespace CounterExampleOfTransSymm

inductive Three: Type where
  | a | b | c

inductive Rel3: Three -> Three -> Prop where
  | ab: Rel3 .a .b
  | cb: Rel3 .c .b

theorem rel3_trans: forall {x y z: Three}, Rel3 x y -> Rel3 y z -> Rel3 x z := by
  intros x y z Hxy Hyz
  cases Hxy
  case ab =>
    cases Hyz
  case cb =>
    cases Hyz


instance: Transitive Rel3 where
  trans {x y z} Hxy Hyz := by
    cases Hxy
    case ab =>
      cases Hyz
    case cb =>
      cases Hyz


example: Not (Transitive (SCl Rel3)) := by
  intros H
  let Hab := SCl.inclusion Rel3.ab
  let Hcb := SCl.inclusion Rel3.cb
  let Hbc := SCl.symm Hcb
  have H2: SCl Rel3 .a .c := by
    apply (SCl Rel3).trans Hab Hbc
  let error := scl_ab_or_ba H2
  cases error
  case inl E => cases E
  case inr E => cases E

end CounterExampleOfTransSymm
