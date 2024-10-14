/-!
# Relations

A relation is just a binary predicate over some type
-/

def Relation (A: Type) := A -> A -> Prop

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

def Relation.super {A: Type} {P: Relation A} {Q: Relation A}
  [inst: P sub_rel Q]: forall {a b: A}, P a b -> Q a b :=
    inst.inclusion

/-!
`SubRel` is it self a poset on all relations
-/
section

instance: SubRel P P where
  inclusion := id

instance: forall {A: Type}, Reflexive (SubRel (A := A)) where
  refl {P} := SubRel.mk P.super


instance: forall {A: Type}, Transitive (SubRel (A := A)) where
  trans {P Q R} {s1 s2} := by
    apply SubRel.mk
    intros a b H
    apply Q.super
    apply P.super
    apply H


theorem sub_equiv: forall {A: Type} {P Q: Relation A},
  [SubRel P Q] -> [SubRel Q P] -> forall {a b: A}, P a b <-> Q a b := by
  intros A P Q s1 s2
  intros a b
  constructor
  . apply s1.inclusion
  . apply s2.inclusion


namespace RelEq

axiom rel_eq: forall {A: Type} {P Q: Relation A},
  P = Q <-> forall (a b: A), P a b <-> Q a b

instance: forall {A: Type}, Antisymmetric (SubRel (A := A)) where
  anti := by
    intros P Q s1 s2
    apply rel_eq.mpr
    intros a b
    apply Iff.intro
    . apply s1.inclusion
    . apply s2.inclusion


end RelEq

end


/---
Reflexive closure
-/
inductive RCl (P: Relation A): Relation A where
  | inclusion: P a b -> RCl P a b
  | refl: RCl P a a

instance: P sub_rel RCl P where
  inclusion := RCl.inclusion

instance: Reflexive (RCl P) where
  refl := RCl.refl

instance [P sub_rel R] [Reflexive R]: RCl P sub_rel R where
  inclusion {a b} H := by
    cases H
    case inclusion Hab =>
      apply P.super
      apply Hab
    case refl => apply R.refl

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

instance: P sub_rel TCl P where
  inclusion := TCl.inclusion

instance: Transitive (TCl P) where
  trans := TCl.trans

instance [P sub_rel R] [Transitive R]: TCl P sub_rel R where
  inclusion {a b} H := by
    induction H
    case inclusion Hab =>
      apply P.super
      apply Hab
    case trans Hab Hbc =>
      apply R.trans
      apply Hab
      apply Hbc


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
        apply P.super
        apply P.trans Hab Hbc
      case refl =>
        apply RCl.inclusion
        apply Hab
    case refl =>
      apply H2


/--
Reflexive and Transitive Closure
-/
inductive RTCl (P: Relation A): Relation A where
  | inclusion: P a b -> RTCl P a b
  | refl: RTCl P a a
  | trans: RTCl P a b -> RTCl P b c -> RTCl P a c

instance: P sub_rel RTCl P where
  inclusion := RTCl.inclusion

instance: Reflexive (RTCl P) where
  refl := RTCl.refl

instance: Transitive (RTCl P) where
  trans := RTCl.trans

instance [P sub_rel Q] [Reflexive Q] [Transitive Q]: RTCl P sub_rel Q where
  inclusion {a b} H := by
    induction H
    case inclusion Hab => apply P.super Hab
    case refl => apply Q.refl
    case trans Hab Hbc =>
      apply Q.trans Hab Hbc


/--
The reflexive and transitive closure is the
reflexive closure of the transitive closure.
-/
instance: RTCl P sub_rel RCl (TCl P) where
  inclusion {a b} H:= by
    induction H
    case inclusion Hab =>
      apply RCl.inclusion
      apply TCl.inclusion
      apply Hab
    case refl =>
      apply RCl.refl
    case trans Hab Hac =>
      apply (RCl (TCl P)).trans Hab Hac


instance: RCl P sub_rel RTCl P where
  inclusion {a b} HR := by
    apply (RCl P).super HR

instance: TCl P sub_rel RTCl P where
  inclusion {a b} HT := by
    apply (TCl P).super HT

instance: RCl (TCl P) sub_rel RTCl P where
  inclusion {a b} HRT:= by
    cases HRT
    case inclusion HT =>
      cases HT
      case inclusion H => apply P.super H
      case trans Hab Hbc =>
        apply (TCl P).super
        apply (TCl P).trans Hab Hbc
    case refl => apply (RTCl P).refl

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
      apply P.super
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
      apply P.super
      apply P.symm Hab
    case refl Hab =>
      apply (RCl P).refl

instance [Symmetric P]: Symmetric (TCl P) where
  symm {a b} H := by
    induction H
    case inclusion Hab =>
      apply P.super
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
