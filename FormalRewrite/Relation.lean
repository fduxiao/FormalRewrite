/-!
# Relations

A relation is just a binary predicate over some type
-/

def Relation (A: Type) := A -> A -> Prop

class Reflexive (P: Relation A) where
  refl: P a a

class Antisymmetric (P: Relation A) where
  anti: P a b -> P b a -> a = b

class Transitive (P: Relation A) where
  trans: P a b -> P b c -> P a c

/--
The defintion of a sub relation
-/
class SubRel (P: Relation A) (Q: Relation A): Prop where
  contained: forall {a b}, P a b -> Q a b

/-!
`SubRel` is it self a poset on all relations
-/
section

instance: forall {A: Type}, Reflexive (SubRel (A := A)) where
  -- refl := (fun {R} => (SubRel.mk (fun {a} {b} H => H)))
  refl := by
    intros R
    apply SubRel.mk
    intros _a _b H
    apply H

end

inductive RefClosure (P: Relation A): Relation A where
  | refl: RefClosure P a a
  | sub: P a b -> RefClosure P a b

structure RelationTri {A: Type} (P: Relation A) where
  a: A
  b: B
  H: P a b


notation: 60 a " -[ " func " ]> " b => func a b
#check (1  -[ Nat.le ]> 2)
#check (Nat.le: Relation Nat)
