/-!
# Relations

A relation is just a binary predicate over some type
-/

def Relation (A: Type) := A -> A -> Prop

class Reflexive (P: Relation A) where
  refl: P a a

def Relation.refl {A: Type} {P: Relation A} [inst: Reflexive P]:
  forall (a: A), P a a := fun _a => inst.refl


class Antisymmetric (P: Relation A) where
  anti: P a b -> P b a -> a = b

def Relation.anti {A: Type} {P: Relation A} [inst: Antisymmetric P]:
  forall {a b: A}, P a b -> P b a -> a = b :=
    fun Hab Hba => inst.anti Hab Hba


class Transitive (P: Relation A) where
  trans: P a b -> P b c -> P a c

def Relation.trans {A: Type} {P: Relation A} [inst: Transitive P]:
  forall {a b c: A}, P a b -> P b c -> P a c :=
    fun Hab Hbc => inst.trans Hab Hbc


class Symmetric (P: Relation A) where
  symm: P a b -> P b a

def Relation.symm {A: Type} {P: Relation A} [inst: Symmetric P]:
  forall {a b: A}, P a b -> P b a := inst.symm


inductive Fold (P: Relation A): Nat -> Relation A where
  | zero: Fold P 0 a a
  | succ: Fold P n a b -> P a b -> Fold P (n+1) a b


inductive Inverse (P: Relation A): Relation A where
  | inv: P a b -> Inverse P b a


def Relation.inv (P: Relation A): P a b -> Inverse P b a:= Inverse.inv


/--
The defintion of a sub relation
-/
class SubRel (P: Relation A) (Q: Relation A): Prop where
  inclusion: forall {a b}, P a b -> Q a b

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


inductive ReflClosure (P: Relation A): Relation A where
  | inclusion: P a b -> ReflClosure P a b
  | refl: ReflClosure P a a

instance: P sub_rel ReflClosure P where
  inclusion := ReflClosure.inclusion

instance: Reflexive (ReflClosure P) where
  refl := ReflClosure.refl

instance [P sub_rel R] [Reflexive R]: ReflClosure P sub_rel R where
  inclusion {a b} Hcl := by
    cases Hcl
    case inclusion H =>
      apply P.super
      apply H
    case refl => apply R.refl


inductive TransitiveClosure (P: Relation A): Relation A where
  | inclusion: P a b -> TransitiveClosure P a b
  | trans: TransitiveClosure P a b -> TransitiveClosure P b c -> TransitiveClosure P a c

instance: P sub_rel TransitiveClosure P where
  inclusion := TransitiveClosure.inclusion

instance: Transitive (TransitiveClosure P) where
  trans := TransitiveClosure.trans

instance [P sub_rel R] [Transitive R]: TransitiveClosure P sub_rel R where
  inclusion {a b} Hcl := by
    induction Hcl
    case inclusion H =>
      apply P.super
      apply H
    case trans Hab Hbc =>
      apply R.trans
      apply Hab
      apply Hbc


inductive SymmetricClosure (P: Relation A): Relation A where
  | inclusion: P a b -> SymmetricClosure P a b
  | symm: SymmetricClosure P a b -> SymmetricClosure P b a

instance: P sub_rel SymmetricClosure P where
  inclusion := SymmetricClosure.inclusion

instance: Symmetric (SymmetricClosure P) where
  symm := SymmetricClosure.symm

instance [P sub_rel R] [Symmetric R]: SymmetricClosure P sub_rel R where
  inclusion {a b} Hcl := by
    induction Hcl
    case inclusion H =>
      apply P.super
      apply H
    case symm Hab =>
      apply R.symm
      apply Hab
