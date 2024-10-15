import FormalRewrite.Relation

open RelEq

class Reducible {A: Type} (R: Relation A) (x: A) where
  reduce: exists y, R x y

def Relation.reducible {A: Type} {R: Relation A} (x: A) [inst: Reducible R x]:
  exists y, R x y := inst.reduce


class Irreducible {A: Type} (R: Relation A) (x: A) where
  irreduce: forall y, Not (R x y)

def Relation.Irreducible {A: Type} {R: Relation A} {x: A} [inst: Irreducible R x]:
  forall y, Not (R x y) := inst.irreduce
