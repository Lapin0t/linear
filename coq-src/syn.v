Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Fin.
From Equations Require Import Equations.

Derive Signature for fin.

(* ssreflect fintype/finfun
   matrix algebra.ssralg
   binop (algebra?)
   canonical structures for the working .
   tuto ds le papier
*)

Set Primitive Projections.

Definition vec (T : Type) (n : nat) : Type := fin n -> T.

Definition vmap {T U} (f : T -> U) {n} (v : vec T n) : vec U n :=
    fun i => f (v i).

Definition vmap2 {T U V} (f : T -> U -> V) {n} (a : vec T n) (b : vec U n) : vec V n :=
    fun i => f (a i) (b i).

Equations vcons {T n} (v : vec T n) (x : T) : vec T (S n) :=
vcons v x F0 := x;
vcons v x (FS i) := v i.

Infix ",," := vcons (at level 40, left associativity).

Inductive R : Type := R0 | R1 | Romega.

Definition radd : R -> R -> R.
Admitted.
Definition rmul : R -> R -> R.
Admitted.
Definition rleq : R -> R -> Prop.
Admitted.

Definition cadd {n} : vec R n -> vec R n -> vec R n := vmap2 radd.
Definition cmul (x : R) {n} : vec R n -> vec R n := vmap (rmul x).
Definition cleq {n} (a b : vec R n) : Prop := forall i, rleq (a i) (b i).

Definition czero {n} : vec R n := fun _ => R0.
Definition cbase {n} : fin n -> vec R n :=
  fun i j => if fin_eq_dec i j then R1 else R0.

Infix "+@" := cadd (at level 50).
Infix "*@" := cmul (at level 40).
Infix "<@" := cleq (at level 70).

Inductive ty : Type :=
  | T0 | T1
  | Tarr : ty -> ty -> ty
  | Tsum : ty -> ty -> ty
  | Ttens : ty -> ty -> ty
  | Tbang : R -> ty -> ty.
  (*| Tbuf : nat -> ty.*)

Infix "-o" := Tarr (at level 30).
Infix "||" := Tsum.
Infix "&&" := Ttens.

Inductive tm {n} (T : vec ty n) (U : vec R n) : ty -> Type :=
  | Var : forall i, U <@ cbase i -> tm T U (T i)
  | Arr_i : forall {A B},
         tm (T ,, A) (U ,, R1) B
      -> tm T U (A -o B)
  | Arr_e : forall {V W A B}, U <@ V +@ W
      -> tm T V (A -o B)
      -> tm T W A
      -> tm T U B
  | One_i : U <@ czero -> tm T U T1
  | One_e : forall {V W A}, U <@ V +@ W
      -> tm T V T1
      -> tm T W A
      -> tm T U A
  | Zer_e : forall {A}, tm T U T0 -> tm T U A
  | Tens_i : forall {V W A B}, U <@ V +@ W
      -> tm T V A
      -> tm T W B
      -> tm T U (A && B)
  | Tens_e : forall {V W A B C}, U <@ V +@ W
      -> tm T V (A && B)
      -> tm (T ,, A ,, B) (W ,, R1 ,, R1) C
      -> tm T U C
  | Sum_i0 : forall {A B}, tm T U A -> tm T U (A || B)
  | Sum_i1 : forall {A B}, tm T U B -> tm T U (A || B)
  | Sum_e : forall {V W A B C}, U <@ V +@ W
      -> tm T V (A || B)
      -> tm (T ,, A) (W ,, R1) C
      -> tm (T ,, B) (W ,, R1) C
      -> tm T U C
  | Bang_i : forall {V r A}, U <@ r *@ V
      -> tm T V A
      -> tm T U (Tbang r A)
  | Bang_e : forall {V W r A C}, U <@ V +@ W
      -> tm T V (Tbang r A)
      -> tm (T ,, A) (W ,, r) C
      -> tm T U C.


Definition stuff n : Type := vec ty n -> vec R n -> ty -> Type.

Record kit (F : forall {n}, stuff n) : Type :=
  mk_kit {
    Kpsh : forall {n} {T : vec ty n} {U V A}, U <@ V
      -> F T U A -> S T V A;
    Kvar : forall {n} {T : vec ty n} {U} (i : fin n), U <@ cbase i
       -> F T U (T i);
    Ktm : forall {n} {T : vec ty n} {U A},
          F T U A -> tm T U A;
    Kwkn : forall {n} {T : vec ty n} {U A B},
          F T U A -> F (T ,, B) (U ,, R0) A;
    }.

Equations lift (F : forall {n}, stuff n) (K : kit F) {}