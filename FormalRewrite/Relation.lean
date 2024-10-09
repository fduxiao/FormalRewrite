/-!
# Relations

A relation is just a binary predicate over some type
-/

def Relation (A: Type) := A -> A -> Prop
structure RelationTri {A: Type} (P: Relation A) where
  a: A
  b: B
  H: P a b


notation: 60 a " -[ " func " ]> " b => func a b
#check (1  -[ Nat.le ]> 2)


/-!
## an example of relation
Let's review some relations in `lean`.
An example of relation is the <= on natural numbers.
-/
namespace MyNat

inductive Nat :=
  | Z: Nat
  | S: Nat -> Nat

open Nat

inductive Nat.le: Nat -> Nat -> Prop :=
  | le_n: Nat.le n n
  | le_S {m: Nat}: forall n, m.le n -> m.le (S n)

open Nat.le

theorem le_Z: forall n, Z.le n := by
  intros n
  induction n
  case Z => apply le_n
  case S n' IHn' =>
    apply le_S
    apply IHn'

theorem le_le_S: forall m n, m.le n -> (S m).le (S n) := by
  intros m n H
  induction H
  case le_n =>
    apply le_n
  case le_S a _H' IHH' =>
    apply le_S
    apply IHH'

theorem le_S_le: forall m n, (S m).le (S n) -> m.le n := by
  intros m n
  induction n
  case Z =>
    intros H
    cases H
    case le_n => apply le_n
    case le_S H' => cases H'
  case S m' IHm' =>
    intros H
    cases H
    case le_n => apply le_n
    case le_S H =>
      cases H
      case le_n => apply le_S; apply le_n
      case le_S H' =>
        apply le_S
        apply IHm'
        apply le_S
        apply H'


/-! Recall the decidability means we can decide whether a `Prop` is true or not -/
def DecidableRel1 (P: Relation A) :=
  exists (f: A -> A -> Bool), forall a b: A, f a b = true <-> P a b

/-!
That means for each `a b: A`, you can decide whether `P a b` or `¬ (P a b)`.

We encode that in lean as an inductive type.
-/

inductive Decidable1 (p: Prop) :=
  | isTrue: p -> Decidable1 p
  | isFalse: ¬p -> Decidable1 p

/-!
Then `DecidableRel1` can be further viewd as follows.
-/

def DecidableRel2 (P: Relation A) := forall a b, Decidable1 (P a b)

/-!
You can read it as if we want the decidability of `p: Prop`, then either
we find `t: p`, or we find `f: ¬p`. This can be viewed as the sum of
two dependent pairs.
-/
def Decidable2 := Or (exists (p: Prop), p) (exists (p: Prop), ¬p)

/-!
In lean, we have a special syntax for such a thing: `typeclasses`.
-/

class inductive Decidable3 (p: Prop) :=
  | isTrue: p -> Decidable3 p
  | isFalse: ¬p -> Decidable3 p

/-!
For example, ¬¬(p ∨ ¬p) is decidable.
-/
theorem dn_em: forall p, ¬¬(p ∨ ¬p) := by
  intros p H
  apply H
  right; intros Hp
  apply H; left; apply Hp


instance : Decidable3 (¬¬(p∨¬p)) := by
  apply Decidable3.isTrue
  apply dn_em

instance : Decidable3 (¬(p ∨ ¬p)) := by
  apply Decidable3.isFalse
  apply dn_em


/-!
The reason for this typeclass is that you are then able to tell `lean`
you can use it as a condition.
-/
#eval if (¬¬(1 <= 2 ∨¬ (1 <= 2))) then true else false
#eval if (¬(1 <= 2 ∨¬ (1 <= 2))) then true else false

/-!
We then take a look of the decidable binary relation.
-/
abbrev DecidableRel3 (p: Relation A) := forall a b: A, Decidable (p a b)

def le_b (m: Nat) (n: Nat): Bool :=
  match m with
  | Z => true
  | S m' => match n with
    | Z => false
    | S n' => le_b m' n'

#check le_Z
theorem le_b_le: forall m n, le_b m n = true -> m.le n := by
  intros m
  induction m
  case Z => intros; apply le_Z
  case S m' IHm' =>
    intros n
    match n with
    | Z => simp [le_b]
    | S n' =>
      simp [le_b]
      intros H
      apply le_le_S
      apply IHm'
      apply H

theorem le_le_b: forall m n, m.le n -> le_b m n = true := by
  intros m
  induction m
  case Z =>
    intros n
    simp [le_b]
  case S m' IHm' =>
    intros n H
    cases n
    case Z => cases H
    case S n' =>
      simp [le_b]
      apply IHm'
      apply le_S_le
      apply H


/-!
We finally can proof `Nat.le` is decidable
-/

instance: DecidableRel3 (Nat.le) := by
  intros m n
  generalize E: (le_b m n) = b
  cases b
  case true =>
    apply isTrue
    apply le_b_le
    apply E
  case false =>
    apply isFalse
    intros H
    let H2 := le_le_b m n H
    rw [E] at H2
    cases H2

end MyNat


#check (Nat.le: Relation Nat)
