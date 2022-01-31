Require Import Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra finset.
From GraphTheory Require Import digraph.
From Coquelicot Require Import Lim_seq Rbar.
From mathcomp.analysis Require Import Rstruct.
From Coq Require Import Logic.Decidable Logic.Classical_Pred_Type.
Require Import definitions.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import sufficiency.
Require Import necessity.

Notation D:= definitions.D.
Notation F:= definitions.F.

Lemma strong_to_weak_sufficiency:
(forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R),
nonempty_nontrivial_graph ->
(0 < F+1 <= #|D|)%N ->
wts_well_behaved A mal init w ->
r_s_robustness (F + 1) (F + 1) ->
Resilient_asymptotic_consensus A mal init w) ->
nonempty_nontrivial_graph ->
(0 < F+1 <= #|D|)%N ->
((forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R), 
wts_well_behaved A mal init w) ->
((forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R),
r_s_robustness (F + 1) (F + 1) ->
Resilient_asymptotic_consensus A mal init w))).
Proof.
intros.
by apply H.
Qed.

Theorem F_total_consensus:
nonempty_nontrivial_graph ->
(0 < F+1 <= #|D|)%N -> 
(forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R),
wts_well_behaved A mal init w) ->
((forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R),
Resilient_asymptotic_consensus A mal init w) <->
r_s_robustness (F + 1) (F + 1)).
Proof.
intros. split.
+ rewrite -contrapositive.
  - assert(((forall (A : D -> bool) (mal : nat -> D -> R) (init : D -> R) (w:nat -> D*D -> R),
    Resilient_asymptotic_consensus A mal init w) -> False) =
    ~ (forall (A : D -> bool) (mal : nat -> D -> R) (init : D -> R) (w:nat -> D*D -> R),
    Resilient_asymptotic_consensus A mal init w)).
    {by unfold not. }
    assert((r_s_robustness (F + 1) (F + 1) -> False) =
    ~ r_s_robustness (F + 1) (F + 1)).
    {by unfold not. }
    rewrite H2 H3. intros. by apply necessity_proof.
  - apply excluded_middle.
+ intros. apply strong_to_weak_sufficiency.
  - apply strong_sufficiency.
  - by [].
  - by [].
  - by [].
  - by [].
Qed.


