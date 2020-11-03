Set Primitive Projections.

Declare Scope skew_scope.
Open Scope skew_scope.

Record proset_raw : Type := PRaw {
  Pobj :> Type ;
  Pleq : Pobj -> Pobj -> Prop
}.

Notation "x <= y" := (@Pleq _ x y)
  (at level 70, no associativity) : skew_scope.

Structure proset_law (P : proset_raw) := PLaw {
  Pleq_refl : forall x : P, x <= x ;
  Pleq_trans : forall {x y z : P}, x <= y -> y <= z -> x <= z
}.

Structure proset_type := Proset {
  Praw :> proset_raw ;
  Plaw : proset_law Praw
}.

Definition Praw_transp (P : proset_raw) : proset_raw := {|
  Pobj := P ;
  Pleq x y := y <= x
|}.

Definition Plaw_transp {P : proset_raw} : proset_law P -> proset_law (Praw_transp P).
refine (fun plaw => {| Pleq_refl x := _ ; Pleq_trans _ _ _ p q := _ |}).
refine (Pleq_refl P plaw x).
refine (Pleq_trans P plaw q p).
Defined.

Definition P_transp (P : proset_type) : proset_type := {|
  Praw := Praw_transp P ;
  Plaw := Plaw_transp P.(Plaw)
|}.

Record monoid_raw := MonoidR {
  M_Praw :> proset_raw ;
  Mzero : M_Praw ;
  Madd : M_Praw -> M_Praw -> M_Praw ;
}.

Notation "0" := (@Mzero _ ) : skew_scope.
Notation "x + y" := (@Madd _ x y) : skew_scope.

Record monoid_mixin (M : monoid_raw) : Prop := MonoidM {
  Mop_mono : forall a b c d : M, a <= b -> c <= d -> a + c <= b + d ;
  Mop_0_l : forall a : M, 0 + a <= a ;
  Mop_0_r : forall a : M, a <= a + 0 ;
  Mop_assoc : forall a b c : M, (a + b) + c <= a + (b + c) ;
}.

Structure monoid_type := {
  Mraw :> monoid_raw ;
  M_Plaw :> proset_law Mraw ;
  Mlaw :> monoid_mixin Mraw
}.

Record semiring_raw := SemiringR {
  SRadd_Mraw :> monoid_raw ;
  SRone : SRadd_Mraw ;
  SRmul : SRadd_Mraw -> SRadd_Mraw -> SRadd_Mraw ;
}.

Definition SRmul_Mraw (SR : semiring_raw) : monoid_raw := {|
    M_Praw := SR ;
    Mzero := SR.(SRone) ;
    Madd := SR.(SRmul)
|}.

Notation "1" := (@SRone _) : skew_scope.
Notation "x * y" := (@SRmul _ x y) : skew_scope.

Record semiring_mixin (SR : semiring_raw) : Prop := {
  SRadd_comm : forall a b : SR, a + b <= b + a ;
  SRmul_0_l : forall a : SR, 0 * a <= 0 ;
  SRmul_0_r : forall a : SR, 0 <= 0 * a ;
  SRaddmul_l : forall a b c : SR, (a + b) * c <= a * c + b * c ;
  SRaddmul_r : forall a b c : SR, a * b + a * c <= a * (b + c) ;
}.

Record semiring_type : Type := {
  SRraw :> semiring_raw ;
  SR_Plaw :> proset_law SRraw ;
  SRadd_Mlaw :> monoid_mixin SRraw ;
  SRmul_Mlaw : monoid_mixin (SRmul_Mraw SRraw) ;
  SRlaw :> semiring_mixin SRraw
}.

Record semimodule_raw (SR : semiring_raw) : Type := {
  SMadd_Mraw :> monoid_raw ;
  SMmul : SR -> SMadd_Mraw -> SMadd_Mraw ;
}.

Notation "x # y" := (@SMmul _ _ x y) (at level 50).

Record semimodule_mixin (SR : semiring_raw) (SM : semimodule_raw SR) : Prop := {
  SMadd_comm : forall a b : SM, a + b <= b + a ;
  SMmul_mono : forall (a b : SR) (c d : SM), a <= b -> c <= d -> a # c <= b # d ;
  SMmul_1_l : forall a : SM, 1 # a <= a ;
  SMmulact : forall (a b : SR) (c : SM), (a * b) # c <= a # (b # c) ;
  SMact_0_l : forall a : SM, 0 # a <= 0 ;
  SMact_0_r : forall a : SR, 0 <= a # (0 : SM) ;
  SMaddact_l : forall (a b : SR) (c : SM), (a + b) # c <= (a # c) + (b # c) ;
  SMaddact_r : forall (a : SR) (b c : SM), (a # b) + (a # c) <= a # (b + c) ;
}.

Record semimodule_type (SR : semiring_type) : Type := {
  SMraw :> semimodule_raw SR ;
  SM_Plaw :> proset_law SMraw ;
  SMadd_Mlaw :> monoid_mixin SMraw ;
  SMlaw :> semimodule_mixin SR SMraw
}.
