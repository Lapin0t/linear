Set Primitive Projections.

From HB Require Import structures.

HB.mixin Record proset_op T := { Pleq : T -> T -> Prop }.
HB.structure Definition proset_raw := { T of proset_op T }.
Notation "x <= y" := (@Pleq _ x y) (at level 70).

HB.mixin Record monoid_op T of proset_raw T := { Mzero : T ; Madd : T -> T -> T }.
HB.structure Definition monoid_raw := { T of proset_raw T & monoid_op T }.
Notation "0" := (@Mzero _).
Notation "x + y" := (@Madd _ x y).

HB.mixin Record semiring_op T of monoid_raw T := { SRone : T ; SRmul : T -> T -> T }.
HB.structure Definition semiring_raw := { T of monoid_raw T & semiring_op T}.
Notation "1" := (@SRone _).
Notation "x * y" := (@SRmul _ x y).

HB.mixin Record proset_ax T of proset_raw T :=
  { Pleq_refl : forall x : T, x <= x ;
    Pleq_trans : forall {x y z : T}, x <= y -> y <= z -> x <= z }.
HB.structure Definition proset := {T of proset_raw T & proset_ax T }.

HB.mixin Record monoid_ax T of proset T & monoid_raw T :=
  { Madd_mono : forall a b c d : T, a <= b -> c <= d -> a + c <= b + d ;
    Madd_0_l : forall a : T, 0 + a <= a ;
    Madd_0_r : forall a : T, a <= a + 0 ;
    Madd_assoc : forall a b c : T, (a + b) + c <= a + (b + c) }.
HB.structure Definition monoid := { T of proset T & monoid_raw T & monoid_ax T }.

HB.mixin Record semiring_ax T of monoid T & semiring_raw T := {
  SRadd_comm : forall a b : T, a + b <= b + a ;
  SRmul_0_l : forall a : T, 0 * a <= 0 ;
  SRmul_0_r : forall a : T, 0 <= 0 * a ;
  SRaddmul_l : forall a b c : T, (a + b) * c <= a * c + b * c ;
  SRaddmul_r : forall a b c : T, a * b + a * c <= a * (b + c) ;
}.
HB.structure Definition semiring := { T of monoid T & semiring_raw T & semiring_ax T }.

(* /!\ upstream bug in hierarchical structures

HB.mixin Record semimodule_op (S : semiring.type) (T : Type) :=
  { SMact : S -> T -> T }.
HB.structure Definition semimodule_raw (S : semiring.type) :=
  { T of monoid_raw T & semimodule_op S T }.

Print semimodule_raw.axioms.
Notation "x # y" := (@SMact _ _ x y) (at level 50).

HB.mixin Record semimodule_ax (S : semiring.type) (T : Type) of semimodule_raw S T := {
  SMadd_comm : forall a : T, a <= a ;
}.
  SMmul_mono : forall (a b : SR) (c d : SM), a <= b -> c <= d -> a # c <= b # d ;
  SMmul_1_l : forall a : SM, 1 # a <= a ;
  SMmulact : forall (a b : SR) (c : SM), (a * b) # c <= a # (b # c) ;
  SMact_0_l : forall a : SM, 0 # a <= 0 ;
  SMact_0_r : forall a : SR, 0 <= a # (0 : SM) ;
  SMaddact_l : forall (a b : SR) (c : SM), (a + b) # c <= (a # c) + (b # c) ;
  SMaddact_r : forall (a : SR) (b c : SM), (a # b) + (a # c) <= a # (b + c) ;
}
*)