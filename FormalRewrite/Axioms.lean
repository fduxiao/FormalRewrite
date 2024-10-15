/-!
From the univalence axiom of HoTT, each Prop should be defined to be retractible.
-/
axiom prop_retractible: forall {P: Prop} {x y: P}, x = y

/-!
Then, in order to prove two relations are the same, just use the homotopy between them.
In lean, this is traditionally called Propositional Extensionality `propext`.

```lean
#check propext
```
-/

#check propext

namespace MyPropExt
axiom propext: forall {P Q: Prop}, (P <-> Q) -> P = Q
end MyPropExt

/-!
We also know that the univalence relation will induce the Functional Extensionality.
In lean, we have `funext` for that.

```lean
#check funext
```
-/
#check funext

namespace MyFunExt
axiom funext: forall {A: Type} {B: A -> Type} {f g: forall x: A, B x},
  (forall x: A, f x = g x) -> f = g
end MyFunExt
