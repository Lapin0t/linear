From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

From HB Require Import structures.
From ExtLib.Data Require Import Nat Fin.
From Equations Require Import Equations.
Require Import skew2.

Definition vec T n := fin n -> T.

Definition zipwith {S T U n} (f : S -> T -> U) (a : vec S n) (b : vec T n) :=
  fun i => f (a i) (b i).

Definition pointwise {S T n} (P : S -> T -> Prop) (a : vec S n) (b : vec T n) :=
  forall i, P (a i) (b i).

Definition const {S n} (x : S) : vec S n := fun _ => x.

HB.instance Definition v_proset_op {n} (P : proset_raw.type) :=
  proset_op.Build (vec P n) (pointwise Pleq).

HB.instance Definition v_proset_ax {n} (P : proset.type) :=
  proset_ax.Build (vec P n)
    (fun x i => Pleq_refl (x i))
    (fun _ _ _ p q i => Pleq_trans _ _ _ (p i) (q i)).

HB.instance Definition v_monoid_op {n} (M : monoid_raw.type) :=
  monoid_op.Build (vec M n) (const Mzero) (zipwith Madd).

HB.instance Definition v_monoid_ax {n} (M : monoid.type) : monoid_ax (vec M n) :=
  monoid_ax.Build (vec M n)
    (fun _ _ _ _ p q i => Madd_mono _ _ _ _ (p i) (q i))
    (fun _ i => Madd_0_l _)
    (fun _ i => Madd_0_r _)
    (fun _ _ _ i => Madd_assoc _ _ _).