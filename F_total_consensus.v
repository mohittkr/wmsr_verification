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

Require Import lemma_1.
Require Import sufficiency.
Require Import necessity.

Notation D:= definitions.D.
Notation F:= definitions.F.


Lemma weak_sufficiency:
(forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R),
nonempty_nontrivial_graph ->
(0 < F+1 <= #|D|)%N ->
wts_well_behaved_general A mal init ->
r_s_robustness (F + 1) (F + 1) ->
Resilient_asymptotic_consensus_general A mal init) ->
nonempty_nontrivial_graph ->
(0 < F+1 <= #|D|)%N ->
((forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R), 
wts_well_behaved_general A mal init) ->
((forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R),
r_s_robustness (F + 1) (F + 1) ->
Resilient_asymptotic_consensus_general A mal init))).
Proof.
intros.
by apply H.
Qed.

Theorem F_total_consensus:
nonempty_nontrivial_graph ->
(0 < F+1 <= #|D|)%N -> 
(forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R),
wts_well_behaved_general A mal init) ->
((forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R),
Resilient_asymptotic_consensus_general A mal init) <->
r_s_robustness (F + 1) (F + 1)).
Proof.
intros. split.
+ rewrite -contrapositive.
  - assert(((forall (A : D -> bool) (mal : nat -> D -> R) (init : D -> R),
    Resilient_asymptotic_consensus_general A mal init) -> False) =
    ~ (forall (A : D -> bool) (mal : nat -> D -> R) (init : D -> R),
    Resilient_asymptotic_consensus_general A mal init)).
    {by unfold not. }
    assert((r_s_robustness (F + 1) (F + 1) -> False) =
    ~ r_s_robustness (F + 1) (F + 1)).
    {by unfold not. }
    rewrite H2 H3. intros. by apply necessity_proof.
  - apply excluded_middle.
+ intros. apply weak_sufficiency.
  - apply sufficiency_proof.
  - by [].
  - by [].
  - by [].
  - by [].
Qed.

