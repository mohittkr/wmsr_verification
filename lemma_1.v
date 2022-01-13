Require Import Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra finset fintype analysis.Rstruct seq.
From GraphTheory Require Import digraph.
From Coquelicot Require Import Lim_seq Rbar.
From Coq Require Import Bool.Bool Arith.PeanoNat.
Require Import definitions.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation D:= definitions.D.
Notation F:= definitions.F.

Definition sorted_Dseq_general (l:seq D) :=
  forall (t:nat) (a b:D) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  a \in l -> b \in l ->
  (index a l < index b l)%N ->
  (x_general mal init A t a <= x_general mal init A t b)%Re.

Lemma andb_triple_inject_left:
  forall (b1 b2 b3:bool), b1 && b2 && b3 -> b1.
Proof.
  intros.
  assert(b1 && b2 /\ b3). {by apply /andP. }
  destruct H0.
  assert(b1 /\ b2). {by apply /andP. }
  by destruct H2.
Qed.

Lemma andb_triple_inject_middle:
  forall (b1 b2 b3:bool), b1 && b2 && b3 -> b2.
Proof.
  intros.
  assert(b1 && b2 /\ b3). {by apply /andP. }
  destruct H0.
  assert(b1 /\ b2). {by apply /andP. }
  by destruct H2.
Qed.

Lemma andb_triple_inject_right:
  forall (b1 b2 b3:bool), b1 && b2 && b3 -> b3.
Proof.
  intros.
  assert(b1 && b2 /\ b3). {by apply /andP. }
  by destruct H0.
Qed.

Hypothesis inclusive_neighbors_sorted_general:
  forall (i:D) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  sorted_Dseq_general (inclusive_neighbor_list i).

Hypothesis incl_sorted_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  sorted_Dseq_general (incl_neigh_minus_extremes i (x_general mal init A) t).

Hypothesis partition_incl_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  inclusive_neighbor_list i = 
  (enum (R_i_less_than_general mal init A i t)) ++
  (incl_neigh_minus_extremes i (x_general mal init A) t) ++
  (enum (R_i_greater_than_general mal init A i t)).


Lemma incl_subset_inclusive_neighbors_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  j \in (incl_neigh_minus_extremes i (x_general mal init A) t) ->
  j \in inclusive_neighbor_list i.
Proof.
intros.
rewrite mem_filter in H.
by apply andb_triple_inject_right in H.
Qed.

Lemma nandb:
  forall (b1 b2:bool), ~~ (b1 && b2) = ~~ b1 || ~~ b2.
Proof.
  intros.
  apply /nandP.
  destruct b1 eqn:E.
  + destruct b2 eqn:E0.
    - simpl.
      unfold not.
      intros.
      destruct H.
      * by [].
      * by [].
    - simpl. by right.
  + simpl. by left.
Qed.

Lemma not_Rlt_Rge:
  forall (a b:R),
  ~~ Rlt_dec a b = Rge_dec a b.
Proof.
  intros.
  destruct Rlt_dec.
  + destruct Rge_dec.
    - simpl. by apply Rlt_not_ge in r.
    - by [].
  + destruct Rge_dec.
    - by [].
    - simpl. by apply Rnot_lt_ge in n.
Qed.

Lemma not_Rgt_Rle:
  forall (a b:R),
  ~~ Rgt_dec a b = Rle_dec a b.
Proof.
  intros.
  destruct Rgt_dec.
  + destruct Rle_dec.
    - simpl. by apply Rgt_not_le in r.
    - by [].
  + destruct Rle_dec.
    - by [].
    - simpl. by apply Rnot_gt_le in n.
Qed.

Lemma not_Rle_Rgt:
  forall (a b:R),
  ~~ Rle_dec a b = Rgt_dec a b.
Proof.
intros.
destruct Rle_dec.
+ destruct Rgt_dec.
  - simpl. by apply Rle_not_gt in r.
  - by [].
+ destruct Rgt_dec.
  - by [].
  - simpl. by apply Rnot_le_gt in n.
Qed.

Lemma incl_set_version_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (incl_neigh_minus_extremes i (x_general mal init A) t) =
  filter (fun (j:D) =>
  (j \notin (R_i_less_than_maybe_not_neighbors_general mal init A i t)) &&
  (j \notin (R_i_greater_than_maybe_not_neighbors_general mal init A i t)))
  (inclusive_neighbor_list i).
Proof.
intros.
apply eq_filter.
unfold eqfun.
intro v.
by rewrite !inE !nandb -!leqNgt not_Rlt_Rge not_Rgt_Rle.
Qed.

Lemma inclusive_neighbors_uniq:
  forall (i:D), uniq (inclusive_neighbor_list i).
Proof.
intros. apply enum_uniq.
Qed.

Lemma incl_uniq_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  uniq (incl_neigh_minus_extremes i (x_general mal init A) t).
Proof.
intros.
apply filter_uniq, inclusive_neighbors_uniq.
Qed.

Lemma i_in_inclusive_neighbors_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  i \in (inclusive_neighbor_list i).
Proof.
intros.
rewrite unfold_in /= -inE set_enum.
apply set1Ur.
Qed.

Lemma i_in_incl_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  i \in (incl_neigh_minus_extremes i (x_general mal init A) t).
Proof.
intros.
rewrite mem_filter.
destruct Rge_dec.
+ destruct Rle_dec.
  - simpl. by apply i_in_inclusive_neighbors_general.
  - contradiction.
+ destruct Rle_dec.
  - contradiction.
  - simpl.
    by apply Rnot_le_lt, Rlt_not_eq in n.
Qed.

(** Added this **)
Lemma list_dissect: forall (i:D) (l : seq D),
  l != [::] -> l = (head i l) :: (behead l).
Proof.
intros. induction l.
+ by [].
+ by rewrite /head /behead.
Qed.

Lemma incl_not_empty_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (incl_neigh_minus_extremes i (x_general mal init A) t) != [::].
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
unfold negb.
destruct (incl == [::]) eqn:E.
+ assert((0 < size incl)%N).
  {apply leq_ltn_trans with (n:=index i incl).
  - apply leq0n.
  - rewrite index_mem Heqincl. apply i_in_incl_general.
  }
  rewrite -size_eq0 in E.
  assert(size incl = 0%N). {by apply /eqP. }
  by rewrite H0 in H.
+ by [].
Qed.

Lemma last_incl_in_incl_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (last (head i (incl_neigh_minus_extremes i (x_general mal init A) t)) (behead (incl_neigh_minus_extremes i (x_general mal init A) t)))
  \in (incl_neigh_minus_extremes i (x_general mal init A) t).
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
rewrite -> list_dissect with (l:=incl) (i:=i) at 3.
rewrite mem_last.
+ by [].
+ rewrite Heqincl.
  apply incl_not_empty_general.
Qed.

Lemma size_incl_not_0_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (0 < size ((incl_neigh_minus_extremes i (x_general mal init A) t)))%N.
Proof.
intros.
destruct (0 == size (incl_neigh_minus_extremes i (x_general mal init A) t))%N eqn:E.
+ assert((0 = size (incl_neigh_minus_extremes i (x_general mal init A) t))%N).
  {apply /eqP. rewrite E. by []. }
  symmetry in H. apply size0nil in H.
  assert(incl_neigh_minus_extremes i (x_general mal init A) t != [::]).
  {apply incl_not_empty_general. }
  by rewrite H in H0.
+ rewrite lt0n.
  apply /eqP.
  unfold not.
  intros.
  by rewrite H in E.
Qed.

Lemma last_incl_is_max_general:
  forall (i k:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  k \in incl_neigh_minus_extremes i (x_general mal init A) t ->
  (x_general mal init A t k <= x_general mal init A t
  (last (head i (incl_neigh_minus_extremes i (x_general mal init A) t))
  (behead (incl_neigh_minus_extremes i (x_general mal init A) t))))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
assert(k == last (head i incl) (behead incl) \/
k != last (head i incl) (behead incl)).
{unfold negb.
destruct (k == last (head i incl) (behead incl)) eqn:E.
+ by left.
+ by right.
}
destruct H0.
+ assert(k = last (head i incl) (behead incl)). {by apply /eqP. }
  rewrite H1. nra.
+ apply incl_sorted_general with (i:=i) (t:=t) (mal:=mal) (init:=init) (A:=A).
  - by rewrite -Heqincl.
  - rewrite Heqincl. apply last_incl_in_incl_general.
  - rewrite -Heqincl (last_nth (head i incl)) -list_dissect.
    * rewrite size_behead index_uniq.
      ++ apply index_ltn.
         rewrite <- cat_take_drop with
         (n0:=(size incl).-1) (s:=incl) in H.
         rewrite mem_cat in H.
         rewrite (drop_nth i) in H.
         rewrite prednK in H. rewrite (drop_size incl) in H.
         rewrite nth_last in H. rewrite mem_seq1 in H.
         assert(last i incl = last (head i incl) (behead incl)).
         {symmetry.
         -- rewrite (last_nth i) -list_dissect.
            by rewrite size_behead nth_last.
         -- rewrite Heqincl. apply (incl_not_empty_general i t mal init A).
         }
         rewrite H1 in H.
         destruct (k == last (head i incl) (behead incl)) eqn:E.
         -- by [].
         -- by rewrite orb_false_r in H.
      ++ rewrite Heqincl. apply size_incl_not_0_general.
      ++ rewrite ltn_predL Heqincl. apply size_incl_not_0_general.
      ++ rewrite ltn_predL Heqincl. apply size_incl_not_0_general.
      ++ rewrite Heqincl. apply incl_uniq_general.
    * rewrite Heqincl. apply incl_not_empty_general.
Qed.

Lemma first_incl_is_min_general:
  forall (i k:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  k \in incl_neigh_minus_extremes i (x_general mal init A) t ->
  (x_general mal init A t (nth i (incl_neigh_minus_extremes i (x_general mal init A) t) 0) <= x_general mal init A t k)%Re.
Proof.
intros.
destruct (k == (nth i (incl_neigh_minus_extremes i (x_general mal init A) t) 0)) eqn:E.
+ assert(k = nth i (incl_neigh_minus_extremes i (x_general mal init A) t) 0).
  {by apply /eqP. }
  rewrite -H0.
  by right.
+ apply incl_sorted_general with (i:=i) (t:=t) (mal:=mal) (init:=init) (A:=A).
  - rewrite mem_nth.
    * by [].
    * apply size_incl_not_0_general.
  - by [].
  - rewrite index_uniq.
    * destruct (0 == index k (incl_neigh_minus_extremes i (x_general mal init A) t))%N eqn:E0.
      ++ assert(0 = index k (incl_neigh_minus_extremes i (x_general mal init A) t))%N.
         {by apply /eqP. }
         rewrite H0 nth_index in E.
         -- assert(k == k = true). {by apply /eqP. }
            by rewrite H1 in E.
         -- by [].
      ++ rewrite eq_sym in E0. by apply neq0_lt0n.
    * apply size_incl_not_0_general.
    * apply incl_uniq_general.
Qed.

Lemma R_i_gt_mnn_subset_R_i_gt_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  j \notin (R_i_greater_than_maybe_not_neighbors_general mal init A i t) ->
  j \notin (R_i_greater_than_general mal init A i t).
Proof.
intros.
rewrite inE.
rewrite inE in H.
destruct (j \in inclusive_neighbor_list i) eqn:E.
+ by rewrite andb_true_r.
+ by rewrite andb_false_r.
Qed.

Lemma R_i_lt_mnn_subset_R_i_lt_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  j \notin (R_i_less_than_maybe_not_neighbors_general mal init A i t) ->
  j \notin (R_i_less_than_general mal init A i t).
Proof.
intros.
rewrite inE.
rewrite inE in H.
destruct (j \in inclusive_neighbor_list i) eqn:E.
+ by rewrite andb_true_r.
+ by rewrite andb_false_r.
Qed.

Lemma andb_triple_eq_false:
  forall (b1 b2 b3:bool),
  b1 && b2 && b3 = false -> ~~b1 || ~~b2 || ~~b3.
Proof.
intros.
destruct b1 eqn:E.
+ destruct b2 eqn:E0.
  - by destruct b3 eqn:E1.
  - by [].
+ by [].
Qed.

Lemma ltn_leq_trans:
  forall (n m p:nat),
  (m < n)%N -> (n <= p)%N -> (m < p)%N.
Proof.
intros.
destruct (n == 0)%N eqn:E.
+ assert((n = 0)%N). {by apply /eqP. }
  by rewrite H1 in H.
+ apply neq0_lt0n in E.
  apply leq_ltn_trans with (n:=n.-1).
  - rewrite -ltnS.
    by rewrite prednK.
  - by rewrite prednK.
Qed.

Lemma in_R_i_gt_bounds_incl_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  j \in R_i_greater_than_general mal init A i t ->
  (x_general mal init A t (last (head i (incl_neigh_minus_extremes i (x_general mal init A) t))
  (behead (incl_neigh_minus_extremes i (x_general mal init A) t))) <= x_general mal init A t j)%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
destruct ((last (head i incl) (behead incl)) \in
R_i_greater_than_general mal init A i t) eqn:E.
+ assert((last (head i incl) (behead incl)) \in incl).
  {rewrite Heqincl. apply last_incl_in_incl_general. }
  rewrite -> Heqincl in H0 at 3.
  rewrite incl_set_version_general mem_filter in H0.
  apply andb_triple_inject_middle in H0.
  apply R_i_gt_mnn_subset_R_i_gt_general in H0.
  unfold negb in H0.
  by rewrite E in H0.
+ rewrite inE in E.
  apply andb_triple_eq_false in E.
  assert((last (head i incl) (behead incl) \in inclusive_neighbor_list i) = true).
  {apply incl_subset_inclusive_neighbors_general with (t:=t) (mal:=mal) (init:=init) (A:=A).
  rewrite Heqincl. apply last_incl_in_incl_general. }
  rewrite H0 /= orb_false_r not_Rgt_Rle -leqNgt in E.
  destruct Rle_dec.
  - apply Rle_trans with (r2:=(x_general mal init A t i)).
    * by [].
    * rewrite inE in H. apply andb_triple_inject_left in H.
      destruct Rgt_dec.
      ++  simpl in H. by apply Rgt_ge, Rge_le in r0.
      ++ by [].
  - simpl in E.
    apply inclusive_neighbors_sorted_general with (i:=i).
    * by [].
    * by [].
    * by [].
    * apply incl_subset_inclusive_neighbors_general with (t:=t) (mal:=mal) (init:=init) (A:=A).
      rewrite Heqincl. apply last_incl_in_incl_general.
    * rewrite inE in H. by apply andb_triple_inject_right in H.
    * rewrite inE in H. apply andb_triple_inject_middle in H.
      by apply leq_ltn_trans with
      (n:=(size (inclusive_neighbor_list i) - F - 1)%N).
Qed.

Lemma in_R_i_lt_bounds_incl_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  j \in R_i_less_than_general mal init A i t ->
  (x_general mal init A t j <= x_general mal init A t (nth i (incl_neigh_minus_extremes i (x_general mal init A) t) 0))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
destruct ((nth i incl 0) \in
R_i_less_than_general mal init A i t) eqn:E.
+ assert((nth i incl 0) \in incl).
  {apply mem_nth. rewrite Heqincl. apply size_incl_not_0_general. }
  rewrite Heqincl incl_set_version_general mem_filter in H0.
  apply andb_triple_inject_left, R_i_lt_mnn_subset_R_i_lt_general in H0.
  rewrite -incl_set_version_general -Heqincl in H0.
  by rewrite E in H0.
+ rewrite inE in E.
  apply andb_triple_eq_false in E.
  assert((nth i incl 0 \in inclusive_neighbor_list i) = true).
  {apply incl_subset_inclusive_neighbors_general with (t:=t) (mal:=mal) (init:=init) (A:=A).
  rewrite Heqincl. apply mem_nth, size_incl_not_0_general. }
  rewrite H0 /= orb_false_r not_Rlt_Rge -leqNgt in E.
  destruct Rge_dec.
  - apply Rle_trans with (r2:=(x_general mal init A t i)).
    * rewrite inE in H. apply andb_triple_inject_left in H.
      destruct Rlt_dec.
      ++ by left.
      ++ by [].
    * rewrite inE in H. apply andb_triple_inject_left in H.
      destruct Rlt_dec.
      ++ simpl in E. by apply Rge_le in r.
      ++ by [].
  - simpl in E.
    rewrite inE in H.
    rewrite Heqincl.
    apply inclusive_neighbors_sorted_general with (t:=t) (i:=i).
    * by [].
    * by [].
    * by [].
    * by apply andb_triple_inject_right in H.
    * by rewrite -Heqincl.
    * apply ltn_leq_trans with (n:=F).
      ++ by apply andb_triple_inject_middle in H.
      ++ by rewrite -Heqincl.
Qed.

Lemma exists_normal_node_in_R_i_gt_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  F_total_malicious_general mal init A ->
  R_i_greater_than_general mal init A i t != Adversary_general A ->
  #|R_i_greater_than_general mal init A i t| == F ->
  (exists (j:D), (j \in (Normal_general A) /\
  j \in R_i_greater_than_general mal init A i t)).
Proof.
intros.
destruct H. destruct H.
assert((exists (j:D), j \in ((Normal_general A) :&: (R_i_greater_than_general mal init A i t))) ->
exists j : D, j \in (Normal_general A) /\ j \in R_i_greater_than_general mal init A i t).
{intro.
elim H4.
intros v H5.
rewrite inE in H5.
exists v.
by apply /andP.
}
apply H4.
apply /set0Pn.
destruct ((Normal_general A) :&: R_i_greater_than_general mal init A i t != set0) eqn:E.
+ by [].
+ assert(Normal_general A :&: R_i_greater_than_general mal init A i t == set0).
  {unfold negb in E.
  by destruct (Normal_general A :&: R_i_greater_than_general mal init A i t == set0).
  }
  rewrite setIC setI_eq0 in H5.
  assert((R_i_greater_than_general mal init A i t) :\: Normal_general A = (R_i_greater_than_general mal init A i t)).
  {by apply /setDidPl. }
  unfold Normal_general in H6.
  rewrite setDDr setDT set0U in H6.
  assert((R_i_greater_than_general mal init A i t) \subset Adversary_general A).
  {apply /setIidPr. by rewrite setIC. }
  assert(#|R_i_greater_than_general mal init A i t| = F). {by apply /eqP. }
  rewrite -H8 in H3.
  assert(R_i_greater_than_general mal init A i t == Adversary_general A).
  {rewrite eqEcard. apply /andP. by split. }
  assert(R_i_greater_than_general mal init A i t = Adversary_general A). {by apply /eqP. }
  rewrite H10 in H0.
  unfold negb in H0.
  assert((Adversary_general A == Adversary_general A) = true). {by apply /eqP. }
  by rewrite H11 in H0.
Qed.

Lemma exists_normal_node_in_R_i_lt_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  F_total_malicious_general mal init A ->
  R_i_less_than_general mal init A i t != Adversary_general A ->
  #|R_i_less_than_general mal init A i t| == F ->
  (exists (j:D), (j \in Normal_general A /\
  j \in R_i_less_than_general mal init A i t)).
Proof.
intros.
destruct H. destruct H.
assert((exists (j:D), j \in (Normal_general A :&: (R_i_less_than_general mal init A i t))) ->
exists j : D, j \in Normal_general A /\ j \in R_i_less_than_general mal init A i t).
{intro. elim H4. intros v H5. rewrite inE in H5. exists v. by apply /andP. }
apply H4.
apply /set0Pn.
destruct (Normal_general A :&: R_i_less_than_general mal init A i t != set0) eqn:E.
+ by [].
+ assert(Normal_general A :&: R_i_less_than_general mal init A i t == set0).
  {unfold negb in E.
  by destruct (Normal_general A :&: R_i_less_than_general mal init A i t == set0).
  }
  rewrite setIC setI_eq0 in H5.
  assert((R_i_less_than_general mal init A i t) :\: Normal_general A = (R_i_less_than_general mal init A i t)).
  {by apply /setDidPl. }
  rewrite setDDr setDT set0U in H6.
  assert((R_i_less_than_general mal init A i t) \subset Adversary_general A).
  {apply /setIidPr. by rewrite setIC. }
  assert(#|R_i_less_than_general mal init A i t| = F). {by apply /eqP. }
  rewrite -H8 in H3.
  assert(R_i_less_than_general mal init A i t == Adversary_general A).
  {rewrite eqEcard. apply /andP. by split. }
  assert(R_i_less_than_general mal init A i t = Adversary_general A). {by apply /eqP. }
  rewrite H10 in H0.
  unfold negb in H0.
  assert((Adversary_general A == Adversary_general A) = true). {by apply /eqP. }
  by rewrite H11 in H0.
Qed.

Lemma filter_index_drop:
forall (i:D) (n:nat) (l:seq D),
  uniq l ->
  filter (fun (j:D) => (n <= index j l)%N) l =
  drop n l.
Proof.
  intros i n.
  induction n as [|n' IHn'].
  + intro. by rewrite drop0 filter_predT.
  + intros l H.
    induction l as [|h t].
    - by [].
    - simpl.
      assert(h == h = true). {by apply /eqP. }
      rewrite H0.
      assert((n' < 0)%N = false). {by rewrite ltn0. }
      rewrite H1.
      rewrite -IHn'.
      assert(uniq (h :: t) = true). {by []. }
      rewrite cons_uniq in H2.
      apply andb_prop in H2.
      destruct H2.
      * apply eq_in_filter.
        unfold prop_in1.
        intros j H4.
        destruct (h == j) eqn:E.
        ++ unfold negb in H2.
           assert(h = j). {by apply /eqP. }
           rewrite -H5 in H4.
           assert((h \in t) = true). {by []. }
           by rewrite H6 in H2.
        ++ by [].
      * rewrite cons_uniq in H.
        apply andb_prop in H.
        by destruct H.
Qed.

Lemma filter_index_take:
forall (i:D) (n:nat) (l:seq D),
  uniq l ->
  filter (fun (j:D) => (index j l < n)%N) l =
  take n l.
Proof.
  intros i n.
  induction n as [|n' IHn'].
  + intro. by rewrite take0 filter_pred0.
  + intros l H.
    induction l as [|h t].
    - by [].
    - simpl.
      assert(h == h = true). {by apply /eqP. }
      rewrite H0.
      assert((0 < n'.+1)%N = true). {by rewrite ltn0Sn. }
      rewrite H1.
      rewrite -IHn'.
      * assert(uniq (h :: t) = true). {by []. }
        rewrite cons_uniq in H2.
        apply andb_prop in H2.
        destruct H2.
        apply /eqP.
        rewrite eqseq_cons H0 /=.
        apply /eqP.
        apply eq_in_filter.
        intros j H4.
        destruct (h == j) eqn:E.
        ++ assert(h = j). {by apply /eqP. }
           rewrite -H5 in H4.
           assert((h \in t) = true). {by []. }
           by rewrite H6 in H2.
        ++ by [].
      * assert(uniq (h :: t) = true). {by []. }
        rewrite cons_uniq in H2.
        apply andb_prop in H2.
        by destruct H2.
Qed.

Lemma R_i_lt_and_incl_disjoint_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  j \in (incl_neigh_minus_extremes i (x_general mal init A) t) ->
  j \notin R_i_less_than_general mal init A i t.
Proof.
intros.
rewrite mem_filter in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rlt_Rge -leqNgt.
apply /orP.
by apply andb_triple_inject_left in H.
Qed.

Lemma R_i_gt_and_incl_disjoint_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  j \in (incl_neigh_minus_extremes i (x_general mal init A) t) ->
  j \notin R_i_greater_than_general mal init A i t.
Proof.
intros.
rewrite mem_filter in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rgt_Rle -leqNgt.
apply /orP.
by apply andb_triple_inject_middle in H.
Qed.

Lemma index_last_incl_general:
  forall (t:nat) (i:D) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (index (last (head i (incl_neigh_minus_extremes i (x_general mal init A) t))
  (behead (incl_neigh_minus_extremes i (x_general mal init A) t))) (inclusive_neighbor_list i) =
  (size (inclusive_neighbor_list i) - #|R_i_greater_than_general mal init A i t| - 1))%N.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
rewrite (partition_incl_general i t mal init A) !index_cat.
assert(last (head i incl) (behead incl)
\in enum (R_i_less_than_general mal init A i t) = false).
{assert((last (head i incl) (behead incl)
\notin enum (R_i_less_than_general mal init A i t))).
{rewrite mem_enum.
apply R_i_lt_and_incl_disjoint_general.
rewrite Heqincl.
apply last_incl_in_incl_general.
}
unfold negb in H.
by destruct (last (head i incl) (behead incl) \in
enum (R_i_less_than_general mal init A i t)) eqn:E.
}
rewrite H.
assert(last (head i incl) (behead incl)
\in incl_neigh_minus_extremes i (x_general mal init A) t = true).
{rewrite -Heqincl.
assert((last (head i incl) (behead incl) \in incl)).
{rewrite Heqincl. apply last_incl_in_incl_general. }
by [].
}
rewrite H0 -Heqincl.
rewrite -> list_dissect with (i:=i) (l:= incl) at 3.
+ rewrite index_last.
  - rewrite size_behead -subn1 !size_cat -subnDA.
    assert(((#|R_i_greater_than_general mal init A i t| + 1) = 
    1 + (#|R_i_greater_than_general mal init A i t|))%N).
    {by rewrite addnC. }
    rewrite H1 -!cardE.
    assert(((size incl + #|R_i_greater_than_general mal init A i t|) -
    (1 + #|R_i_greater_than_general mal init A i t|) = size incl - 1)%N).
    {by rewrite subnDr. }
    assert((#|R_i_less_than_general mal init A i t| + (size incl + #|R_i_greater_than_general mal init A i t|) -
    (1 + #|R_i_greater_than_general mal init A i t|))%N = 
    (#|R_i_less_than_general mal init A i t| + ((size incl + #|R_i_greater_than_general mal init A i t|) -
    (1 + #|R_i_greater_than_general mal init A i t|)))%N).
    {rewrite addnBA.
    * by [].
    * rewrite leq_add2r Heqincl.
      apply size_incl_not_0_general.
    }
    by rewrite H3 subnDr.
  - rewrite -list_dissect Heqincl.
    * apply incl_uniq_general.
    * apply incl_not_empty_general.
+ rewrite Heqincl. apply incl_not_empty_general.
Qed.

Lemma index_first_incl_general:
  forall (t:nat) (i:D) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (index (nth i (incl_neigh_minus_extremes i (x_general mal init A) t) 0)
  (inclusive_neighbor_list i) = #|R_i_less_than_general mal init A i t|)%N.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
rewrite (partition_incl_general i t mal init A) !index_cat.
assert(nth i incl 0 \in enum (R_i_less_than_general mal init A i t) = false).
{assert(nth i incl 0 \notin enum (R_i_less_than_general mal init A i t)).
{rewrite mem_enum.
apply R_i_lt_and_incl_disjoint_general.
rewrite Heqincl.
apply mem_nth, size_incl_not_0_general.
}
by destruct (nth i incl 0 \in
enum (R_i_less_than_general mal init A i t)) eqn:E.
}
rewrite H.
assert(nth i incl 0 \in incl_neigh_minus_extremes i (x_general mal init A) t = true).
{rewrite -Heqincl.
assert((nth i incl 0 \in incl)).
{rewrite Heqincl. apply mem_nth, size_incl_not_0_general. }
by [].
}
rewrite H0 -Heqincl -cardE index_uniq.
+ by rewrite addn0.
+ rewrite Heqincl. apply size_incl_not_0_general.
+ rewrite Heqincl. apply incl_uniq_general.
Qed.

Lemma card_R_i_gt_lt_F_exchange_last_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (#|R_i_greater_than_general mal init A i t| < F)%N ->
  ((x_general mal init A t (last (head i (incl_neigh_minus_extremes i (x_general mal init A) t))
  (behead (incl_neigh_minus_extremes i (x_general mal init A) t)))) = (x_general mal init A t i))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
assert((index (last (head i incl) (behead incl))
(inclusive_neighbor_list i) =
(size (inclusive_neighbor_list i) - #|R_i_greater_than_general mal init A i t| - 1))%N).
{rewrite Heqincl. apply index_last_incl_general. }
assert(((#|R_i_greater_than_general mal init A i t| + 1) < (F + 1))%N).
{unfold leq. unfold leq in H.
assert(((#|R_i_greater_than_general mal init A i t|.+1 - F) = 0)%N).
{by apply /eqP. }
rewrite <- H1 at 3.
by rewrite !addn1 subSS.
}
assert(#|incl| = size incl).
{apply /card_uniqP.
rewrite Heqincl.
apply incl_uniq_general.
}
assert(i != (last (head i incl) (behead incl)) ->
(size (inclusive_neighbor_list i) - (F + 1) <
size (inclusive_neighbor_list i) - (#|R_i_greater_than_general mal init A i t| + 1))%N).
{intros.
apply ltn_sub2l with (p:=(size (inclusive_neighbor_list i))%N) in H1.
+ by [].
+ rewrite (partition_incl_general i t mal init A) !size_cat -!cardE addnA addnCAC.
  apply ltn_leq_trans with (n:=(#|R_i_greater_than_general mal init A i t| +
  (size (incl_neigh_minus_extremes i (x_general mal init A) t)))%N).
  - rewrite -ltn_psubLR.
    * rewrite -addnBAC.
      ++ rewrite subnn addnC addn0 -Heqincl -H2.
         apply /card_gt1P.
         exists i. exists (last (head i incl) (behead incl)).
         split.
         -- rewrite Heqincl. apply i_in_incl_general.
         -- rewrite Heqincl. apply last_incl_in_incl_general.
         -- by [].
      ++ rewrite leq_eqVlt. apply /orP. by left.
    * apply size_incl_not_0_general.
  - by rewrite leq_addr.
}
apply Rle_antisym.
+ destruct (i == (last (head i incl) (behead incl)))%N eqn:E.
  - assert(i = (last (head i incl) (behead incl)))%N.
    {by apply /eqP. }
    rewrite -H4.
    by right.
  - assert((last (head i incl) (behead incl)) \notin
    R_i_greater_than_general mal init A i t).
    {apply R_i_gt_and_incl_disjoint_general. rewrite Heqincl.
    apply last_incl_in_incl_general.
    }
    rewrite inE in H4.
    assert((last (head i incl) (behead incl) \in
    inclusive_neighbor_list i) = true).
    {apply incl_subset_inclusive_neighbors_general
    with (t:=t) (mal:=mal) (init:= init) (A:=A).
    rewrite Heqincl. apply last_incl_in_incl_general.
    }
    rewrite H5 in H4.
    assert(true). {by []. }
    apply H3 in H6.
    rewrite !subnDA -H0 in H6.
    assert((size (inclusive_neighbor_list i) - F - 1 <
    index (last (head i incl) (behead incl))
    (inclusive_neighbor_list i))%N = true).
    {by []. }
    rewrite H7 !andb_true_r not_Rgt_Rle in H4.
    by destruct Rle_dec.
+ rewrite Heqincl. apply last_incl_is_max_general, i_in_incl_general.
Qed.

Lemma card_R_i_lt_lt_F_exchange_first_general:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (#|R_i_less_than_general mal init A i t| < F)%N ->
  ((x_general mal init A t (nth i (incl_neigh_minus_extremes i (x_general mal init A) t) 0)) = (x_general mal init A t i))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
assert((index (nth i incl 0) (inclusive_neighbor_list i) =
#|R_i_less_than_general mal init A i t|)%N).
{rewrite Heqincl. apply index_first_incl_general. }
assert(((#|R_i_less_than_general mal init A i t| + 1) < (F + 1))%N).
{unfold leq. unfold leq in H.
assert(((#|R_i_less_than_general mal init A i t|.+1 - F) = 0)%N).
{by apply /eqP. }
rewrite <- H1 at 3.
by rewrite !addn1 subSS.
}
assert(#|incl| = size incl).
{apply /card_uniqP.
rewrite Heqincl.
apply incl_uniq_general.
}
apply Rle_antisym.
+ destruct (i == (nth i incl 0))%N eqn:E.
  - assert(i = (nth i incl 0))%N.
    {by apply /eqP. }
    rewrite -H3.
    by right.
  - apply inclusive_neighbors_sorted_general with (i:=i).
    * by [].
    * by [].
    * by [].
    * apply incl_subset_inclusive_neighbors_general with (t:=t) (mal:=mal) (init:=init) (A:=A).
      rewrite Heqincl. apply mem_nth, size_incl_not_0_general.
    * by apply i_in_inclusive_neighbors_general.
    * rewrite (partition_incl_general i t mal init A) !index_cat.
      assert((nth i incl 0) \notin enum (R_i_less_than_general mal init A i t)).
      {rewrite mem_enum. apply R_i_lt_and_incl_disjoint_general. rewrite Heqincl.
      apply mem_nth, size_incl_not_0_general.
      }
      assert(nth i incl 0 \in enum (R_i_less_than_general mal init A i t) = false).
      {by destruct (nth i incl 0 \in enum (R_i_less_than_general mal init A i t)) eqn:E0. }
      assert(nth i incl 0 \in incl_neigh_minus_extremes i (x_general mal init A) t = true).
      {rewrite Heqincl. apply mem_nth, size_incl_not_0_general. }
      assert(i \notin enum (R_i_less_than_general mal init A i t)).
      {rewrite mem_enum. apply R_i_lt_and_incl_disjoint_general, i_in_incl_general. }
      assert(i \in enum (R_i_less_than_general mal init A i t) = false).
      {by destruct (i \in enum (R_i_less_than_general mal init A i t)). }
      assert(i \in incl_neigh_minus_extremes i (x_general mal init A) t = true).
      {apply i_in_incl_general. }
      rewrite H4 H5 H7 H8 -!cardE Heqincl index_uniq.
      ++ rewrite addn0 -ltn_subLR.
         -- rewrite subnn.
            destruct (index i (incl_neigh_minus_extremes i (x_general mal init A) t) ==
            0)%N eqn:E0.
            ** assert(index i (incl_neigh_minus_extremes i (x_general mal init A) t) = 0)%N.
               {by apply /eqP. }
               rewrite -H9 Heqincl nth_index in E.
               +++ assert(i == i = true). {by apply /eqP. }
                   by rewrite H10 in E.
               +++ apply i_in_incl_general.
            ** by rewrite neq0_lt0n.
         -- by [].
      ++ apply size_incl_not_0_general.
      ++ apply incl_uniq_general.
+ assert((nth i incl 0) \notin R_i_less_than_general mal init A i t).
  {apply R_i_lt_and_incl_disjoint_general. rewrite Heqincl.
  apply mem_nth, size_incl_not_0_general.
  }
  rewrite inE in H3.
  assert(((nth i incl 0) \in inclusive_neighbor_list i) = true).
  {apply incl_subset_inclusive_neighbors_general with (t:=t) (mal:=mal) (init:=init) (A:=A).
  rewrite Heqincl. apply mem_nth, size_incl_not_0_general.
  }
  rewrite H4 in H3.
  assert((index (nth i incl 0) (inclusive_neighbor_list i) < F)%N = true).
  {apply leq_ltn_trans with (n:=#|R_i_less_than_general mal init A i t|).
  * rewrite (partition_incl_general i t mal init A) !index_cat.
    assert(nth i incl 0 \in enum (R_i_less_than_general mal init A i t) = false).
    {assert((nth i incl 0 \notin enum (R_i_less_than_general mal init A i t))).
    {rewrite mem_enum. apply R_i_lt_and_incl_disjoint_general.
    rewrite Heqincl. apply mem_nth, size_incl_not_0_general. }
    by destruct (nth i incl 0 \in enum (R_i_less_than_general mal init A i t)) eqn:E0.
    }
    rewrite H5.
    assert(nth i incl 0 \in incl_neigh_minus_extremes i (x_general mal init A) t = true).
    {rewrite Heqincl. apply mem_nth, size_incl_not_0_general. }
    rewrite H6 Heqincl index_uniq.
    ++ by rewrite -cardE addn0.
    ++ apply size_incl_not_0_general.
    ++ apply incl_uniq_general.
  * by [].
  }
  rewrite H5 !andb_true_r not_Rlt_Rge in H3.
  apply Rge_le.
  by destruct Rge_dec.
Qed.

Lemma in_normal_subset_general:
  forall (i:D) (l : seq D) (A:D -> bool),
  l != [::] -> 
  (forall (a:D), a \in l -> a \in (enum (Normal_general A))) ->
  last (head i l) (behead l) \in Normal_general A.
Proof.
  intros.
  assert(last (head i l) (behead l) \in [set v | v \in enum (Normal_general A)] ->
  last (head i l) (behead l) \in (Normal_general A)).
  {by rewrite set_enum. }
  apply H1.
  rewrite inE.
  apply H0.
  assert(l = (head i l)::(behead l)). {by rewrite -list_dissect. }
  rewrite -> H2 at 3.
  apply mem_last.
Qed.

Lemma in_normal_subset_0_general: forall (i:D) (l : seq D) (A : D -> bool),
  l != [::] -> 
  (forall (a:D), a \in l -> a \in enum (Normal_general A)) ->
  nth i l 0 \in (Normal_general A).
Proof.
  intros.
  rewrite -mem_enum.
  apply H0.
  rewrite mem_nth.
  + by [].
  + destruct (size l == 0)%N eqn:E.
    - rewrite size_eq0 in E.
      by rewrite E in H.
    - by rewrite neq0_lt0n.
Qed.

Theorem Normal_adversary_disjoint_general:
forall (i:D) (A:D -> bool),
i \in Normal_general A <-> i \notin Adversary_general A.
Proof.
intros.
unfold iff.
split.
+ rewrite inE. intros.
  rewrite !inE andb_true_r in H.
  unfold negb.
  destruct (i \in Adversary_general A) eqn:E.
  - unfold Adversary_general in E.
    rewrite inE in E.
    assert(G: (A i = true)).
    {apply /eqP. by rewrite E. }
    rewrite G in H.
    discriminate.
  - by [].
+ rewrite inE. intros.
  unfold Normal_general.
  by rewrite !inE andb_true_r.
Qed.

Lemma R_i_gt_bounded_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (#|R_i_greater_than_general mal init A i t| <= F)%N.
Proof.
  intros.
  destruct (F < (size (inclusive_neighbor_list i)))%N eqn:E.
  + assert(F = size (filter (fun (j:D) => (index j (inclusive_neighbor_list i) >
    ((size (inclusive_neighbor_list i)) - F - 1))%N)
    (inclusive_neighbor_list i))).
    {rewrite subn1.
    rewrite filter_index_drop.
    - rewrite prednK.
      * rewrite size_drop subKn.
        ++ by [].
        ++ by apply ltnW in E.
      * by rewrite subn_gt0.
    - by [].
    - apply inclusive_neighbors_uniq.
    }
    rewrite H cardE.
    apply uniq_leq_size.
    - apply enum_uniq.
    - intros v H1.
      rewrite mem_filter.
      rewrite mem_enum inE in H1.
      apply /andP.
      split.
      * by apply andb_triple_inject_middle in H1.
      * by apply andb_triple_inject_right in H1.
  + assert((size (inclusive_neighbor_list i) <= F)%N).
    {rewrite leqNgt. unfold negb. by rewrite E. }
    apply leq_trans with (n:=(size (inclusive_neighbor_list i))%N).
    - rewrite cardE.
      apply uniq_leq_size.
      * apply enum_uniq.
      * intros v H0.
        rewrite mem_enum inE in H0.
        apply andb_triple_inject_right in H0.
      * by [].
    - by [].
Qed.

Lemma R_i_lt_bounded_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  (#|R_i_less_than_general mal init A i t| <= F)%N.
Proof.
intros.
destruct (F < (size (inclusive_neighbor_list i)))%N eqn:E.
+ assert(F = size (filter (fun (j:D) => (index j (inclusive_neighbor_list i) < F)%N)
  (inclusive_neighbor_list i))).
  {rewrite filter_index_take.
  - by rewrite size_take E.
  - by [].
  - apply inclusive_neighbors_uniq.
  }
  rewrite H cardE.
  apply uniq_leq_size.
  - apply enum_uniq.
  - intros v H1.
    rewrite mem_filter.
    rewrite mem_enum inE in H1.
    apply /andP.
    split.
    * by apply andb_triple_inject_middle in H1.
    * by apply andb_triple_inject_right in H1.
+ assert((size (inclusive_neighbor_list i) <= F)%N).
  {rewrite leqNgt. unfold negb. by rewrite E. }
  apply leq_trans with (n:=(size (inclusive_neighbor_list i))%N).
  - rewrite cardE.
    apply uniq_leq_size.
    * apply enum_uniq.
    * intros v H0.
      rewrite mem_enum inE in H0.
      apply andb_triple_inject_right in H0.
    * by [].
  - by [].
Qed.

Lemma exists_j2_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  i \in Normal_general A ->
  (exists (j2:D), j2 \in (inclusive_neighbor_list i) /\ j2 \in Normal_general A /\
  forall (k:D), k \in (incl_neigh_minus_extremes i (x_general mal init A) t) ->
  ((x_general mal init A t k) <= (x_general mal init A t j2))%Re).
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
assert((#|R_i_greater_than_general mal init A i t| <= F)%N \/
(#|R_i_greater_than_general mal init A i t| > F)%N).
{apply /orP. destruct (#|R_i_greater_than_general mal init A i t| <= F)%N eqn:E.
+ by [].
+ by rewrite /= leqNgt ltnS E.
}
destruct H2.
+ assert ((#|R_i_greater_than_general mal init A i t| == F)%N \/
  (#|R_i_greater_than_general mal init A i t| < F)%N).
  {apply /orP. by rewrite -leq_eqVlt. }
  destruct H3.
  - assert(R_i_greater_than_general mal init A i t == Adversary_general A \/
    R_i_greater_than_general mal init A i t != Adversary_general A).
    {apply /orP.
    by destruct (R_i_greater_than_general mal init A i t == Adversary_general A).
    }
    destruct H4. (** the j2 here is the last elt of J\R_i[t] **)
    * exists (last (head i incl) (behead incl)).
      split.
      ++ apply incl_subset_inclusive_neighbors_general with (mal:=mal) (init:=init) (A:=A) (t:=t).
         rewrite Heqincl.
         apply last_incl_in_incl_general.
      ++ split.
         -- assert(R_i_greater_than_general mal init A i t = Adversary_general A).
            {by apply /eqP. }
            apply in_normal_subset_general.
            ** rewrite Heqincl. apply incl_not_empty_general.
            ** intros.
               rewrite Heqincl incl_set_version_general mem_filter in H6.
               assert(a \notin R_i_greater_than_general mal init A i t).
               {apply andb_triple_inject_middle in H6.
               by apply R_i_gt_mnn_subset_R_i_gt_general in H6.
               }
               rewrite H5 in H7.
               apply Normal_adversary_disjoint_general in H7.
               by rewrite mem_enum.
         -- intros. rewrite Heqincl. apply last_incl_is_max_general.
            rewrite -Heqincl. exact H5.
    * assert((exists (j:D), j \in Normal_general A /\
      j \in R_i_greater_than_general mal init A i t)).
      {by apply exists_normal_node_in_R_i_gt_general. }
      elim H5. intros v H6.
      exists v.
      destruct H6.
      split.
      ++ rewrite inE in H7. by apply andb_triple_inject_right in H7.
      ++ split.
         -- exact H6.
         -- intros.
            apply Rle_trans with (r2:=x_general mal init A t
            (last (head i incl) (behead incl))).
            ** rewrite Heqincl. rewrite Heqincl in H8.
               by apply last_incl_is_max_general.
            ** rewrite Heqincl. rewrite Heqincl in H8.
               by apply in_R_i_gt_bounds_incl_general.
  - exists i.
    split.
    * by apply i_in_inclusive_neighbors_general.
    * split.
      ++ by [].
      ++ rewrite -card_R_i_gt_lt_F_exchange_last_general.
         -- rewrite Heqincl. intros. by apply last_incl_is_max_general.
         -- by [].
         -- by [].
+ assert((#|R_i_greater_than_general mal init A i t| <= F)%N). {apply R_i_gt_bounded_general. }
  assert((F != #|R_i_greater_than_general mal init A i t|)%N).
  {rewrite neq_ltn. apply /orP. by left. }
  assert((F < F)%N).
  {apply ltn_trans with (n:=#|R_i_greater_than_general mal init A i t|).
  - by [].
  - rewrite ltn_neqAle.
    apply /andP.
    split.
    * rewrite neq_ltn. apply /orP. by right.
    * by [].
  }
  by rewrite ltnn in H5.
Qed.

Lemma exists_j1_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  i \in Normal_general A ->
  (exists (j1:D), j1 \in (inclusive_neighbor_list i) /\ j1 \in Normal_general A /\
  forall (k:D), k \in (incl_neigh_minus_extremes i (x_general mal init A) t) ->
  ((x_general mal init A t j1) <= (x_general mal init A t k))%Re).
Proof.
intros.
remember (incl_neigh_minus_extremes i (x_general mal init A) t) as incl.
assert((#|R_i_less_than_general mal init A i t| <= F)%N).
{apply R_i_lt_bounded_general. }
rewrite leq_eqVlt in H2.
assert(R_i_less_than_general mal init A i t == Adversary_general A \/
R_i_less_than_general mal init A i t != Adversary_general A).
{apply /orP. by destruct (R_i_less_than_general mal init A i t == Adversary_general A). }
assert((#|R_i_less_than_general mal init A i t| == F)
\/ (#|R_i_less_than_general mal init A i t| < F)%N). {by apply /orP. }
destruct H4.
+ destruct H3.
  - assert(R_i_less_than_general mal init A i t = Adversary_general A). {by apply /eqP. }
    exists (nth i incl 0%N).
    split.
    * assert(nth i incl 0 \in incl).
      {rewrite mem_nth. 
      ++ by [].
      ++ rewrite Heqincl. apply size_incl_not_0_general.
      }
      rewrite Heqincl in H6.
      apply incl_subset_inclusive_neighbors_general in H6.
      by rewrite Heqincl.
    * split.
      ++ apply in_normal_subset_0_general.
         -- rewrite Heqincl. apply incl_not_empty_general.
         -- intros.
            rewrite Heqincl incl_set_version_general mem_filter in H6.
            assert(a \notin R_i_less_than_general mal init A i t).
            {apply andb_triple_inject_left in H6.
            by apply R_i_lt_mnn_subset_R_i_lt_general.
            }
            rewrite H5 in H7.
            apply Normal_adversary_disjoint_general in H7.
            by rewrite mem_enum.
      ++ rewrite Heqincl. intros.
         by apply first_incl_is_min_general with (i:=i) (t:=t).
  - assert((exists (j:D), j \in Normal_general A /\
    j \in R_i_less_than_general mal init A i t)).
    {by apply exists_normal_node_in_R_i_lt_general. }
    elim H5.
    intros v H6.
    exists v.
    destruct H6.
    split.
    * assert(v \in R_i_less_than_general mal init A i t). {by []. }
      rewrite inE in H8.
      by apply andb_triple_inject_right in H8.
    * split.
      ++ by [].
      ++ intros.
         apply Rle_trans with (r2:=x_general mal init A t (nth i incl 0)).
         -- rewrite Heqincl. by apply in_R_i_lt_bounds_incl_general.
         -- destruct (k == (nth i incl 0)) eqn:E.
            ** assert(k = nth i incl 0). {by apply /eqP. }
               rewrite -H9. by right.
            ** rewrite Heqincl. apply incl_sorted_general with (mal:=mal) (init:=init) (A:=A) (i:=i) (t:=t).
               +++ apply mem_nth, size_incl_not_0_general.
               +++ by rewrite -Heqincl.
               +++ rewrite index_uniq.
                   --- destruct (0 == index k (incl_neigh_minus_extremes i (x_general mal init A) t))%N eqn:E0.
                       *** assert(0 = index k (incl_neigh_minus_extremes i (x_general mal init A) t))%N.
                           {by apply /eqP. }
                           assert(k == k = true). {by apply /eqP. }
                           rewrite H9 -Heqincl nth_index in E.
                           ++++ by rewrite E in H10.
                           ++++ by [].
                       *** rewrite eq_sym in E0.
                           by apply neq0_lt0n.
                   --- apply size_incl_not_0_general.
                   --- apply incl_uniq_general.
    * exists i. split.
      ++ by apply i_in_inclusive_neighbors_general.
      ++ split.
         -- by [].
         -- rewrite -card_R_i_lt_lt_F_exchange_first_general.
            ** rewrite Heqincl. intros. by apply first_incl_is_min_general.
            ** by [].
            ** by [].
Qed.

Theorem w_coeff_sum_to_1_implies_sum_eq_orig_general:
  forall (i:D) (t:nat) (r:R) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  sum_f_R0 (fun n : nat =>
  w t (i, nth i (incl_neigh_minus_extremes i (x_general mal init A) t) n))
  (size (incl_neigh_minus_extremes i (x_general mal init A) t) - 1) = 1 -> (sum_f_R0 (fun n:nat =>
  ((w t (i,(nth i (incl_neigh_minus_extremes i (x_general mal init A) t) n))) * r)%Re)
  ((size (incl_neigh_minus_extremes i (x_general mal init A) t))-1) = r).
Proof.
intros. by rewrite -scal_sum H Rmult_1_r.
Qed.

Lemma lem_1_general:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool),
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  i \in Normal_general A ->
  ((x_general mal init A (t+1) i <= M_general mal init A t)%Re /\
  (m_general mal init A t <= x_general mal init A (t+1) i)%Re).
Proof.
intros. split.
assert(A i = false).
{apply Normal_adversary_disjoint_general in H1.
rewrite inE in H1.
unfold negb in H1.
by destruct (A i).
}
+ induction t as [|t' IHt'].
  - assert(aux1: i \in Normal_general A). {by []. }
    assert(aux2: wts_well_behaved_general A mal init). {by []. }
    rewrite /wts_well_behaved_general in H0.
    destruct H0 as [a H0].
    destruct H0. destruct H3.
    specialize (H4 0%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig_general
    with (r:=(M_general mal init A 0)) (mal:=mal) (init:=init) (A:=A) (i:=i) (t:=0%N).
    rewrite /= H2.
    apply sum_Rle.
    intros n H7.
    rewrite Rmult_comm.
    apply Rmult_le_compat_l.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x_general mal init A) 0) = 
         (size (incl_neigh_minus_extremes i (x_general mal init A) 0) - 1).+1).
         {rewrite subn1 prednK.
         -- by [].
         -- apply size_incl_not_0_general.
         } rewrite H8 ltnS. by apply /leP.
    * unfold M_general.
      assert((exists (j2:D), j2 \in (inclusive_neighbor_list i) /\
      j2 \in Normal_general A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x_general mal init A) 0) ->
      ((x_general mal init A 0 k) <= (x_general mal init A 0 j2))%Re)).
      {by apply exists_j2_general. }
      elim H8.
      intros v H9.
      destruct H9. destruct H10.
      apply Rle_trans with (r2:= (x_general mal init A 0 v)).
      ++ apply H11, mem_nth.
         assert((n <= size (incl_neigh_minus_extremes i (x_general mal init A) 0) - 1)%N).
         {by apply /leP. }
         rewrite subn1 -ltnS prednK in H12.
         -- by [].
         -- rewrite -has_predT.
            apply /hasP.
            exists i.
            ** apply i_in_incl_general.
            ** by [].
      ++ remember [seq x_general mal init A 0 i | i <- enum (Normal_general A)] as x_incl.
         rewrite <- nth_index with (x0:=0) (x:= x_general mal init A 0 v)
         (s:=x_incl). 
         -- apply /RlebP.
            apply bigmaxr_ler with (x0:=0) (s:=x_incl)
            (i0:=(index (x_general mal init A 0 v) x_incl)).
            rewrite Heqx_incl index_mem.
            apply map_f. by rewrite mem_enum.
         -- rewrite Heqx_incl.
            apply map_f. by rewrite mem_enum.
    * by [].
  - rewrite /= H2.
    assert(aux1: i \in Normal_general A). {by []. }
    assert(aux2: wts_well_behaved_general A mal init). {by []. }
    rewrite /wts_well_behaved_general in H0.
    destruct H0 as [a H0].
    destruct H0. destruct H3.
    specialize (H4 (t'.+1)%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig_general with
    (init:=init) (mal:=mal) (A:=A) (r:=(M_general mal init A t'.+1)) (i:=i) (t:=t'.+1%N).
    rewrite -addnE addn1.
    apply sum_Rle.
    intros n H7.
    rewrite Rmult_comm.
    apply Rmult_le_compat_l.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x_general mal init A) (t'.+1)) = 
         (size (incl_neigh_minus_extremes i (x_general mal init A) (t'.+1)) - 1).+1).
         {rewrite subn1 prednK.
         -- by [].
         -- apply size_incl_not_0_general.
         }
         rewrite H8 ltnS.
         by apply /leP.
    * assert((exists (j2:D), j2 \in (inclusive_neighbor_list i) /\
      j2 \in Normal_general A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x_general mal init A) (t'.+1)) ->
      ((x_general mal init A (t'.+1) k) <= (x_general mal init A (t'.+1) j2))%Re)).
      {by apply exists_j2_general. }
      elim H8.
      intros v H9.
      apply Rle_trans with (r2:= (x_general mal init A (t'.+1) v)).
      ++ destruct H9. destruct H10.
         apply H11. rewrite mem_nth.
         -- by [].
         -- assert((n <= size (incl_neigh_minus_extremes i (x_general mal init A) (t'.+1)) - 1)%N).
            {by apply /leP. }
            rewrite subn1 -ltnS prednK in H12.
            ** by []. 
            ** rewrite -has_predT.
               apply /hasP.
               exists i.
               +++ apply i_in_incl_general.
               +++ by [].
      ++ unfold M_general. destruct H9. destruct H10.
         remember [seq x_general mal init A (t'.+1) i | i <- enum (Normal_general A)] as x_incl.
         rewrite <- nth_index with (x0:=0) (x:= x_general mal init A (t'.+1) v)
         (s:=x_incl). 
         -- apply /RlebP. unfold M_general.
            apply bigmaxr_ler with (x0:=0)
            (s:=x_incl)
            (i0:=(index (x_general mal init A (t'.+1) v) x_incl)).
            rewrite Heqx_incl index_mem.
            apply map_f.
            by rewrite mem_enum.
         -- rewrite Heqx_incl.
            apply map_f. by rewrite mem_enum.
      ++ by [].
+ assert(A i = false).
  {apply Normal_adversary_disjoint_general in H1.
  rewrite inE in H1.
  unfold negb in H1.
  by destruct (A i).
  }
  induction t as [|t' IHt'].
  - assert(aux1: i \in Normal_general A). {by []. }
    assert(aux2: wts_well_behaved_general A mal init). {by []. }
    rewrite /wts_well_behaved_general in H0.
    destruct H0 as [a H0]. destruct H0. destruct H3.
    specialize (H4 0%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig_general
    with (r:=(m_general mal init A 0)) (mal:=mal) (init:=init) (A:=A) (i:=i) (t:=0%N).
    rewrite /= H2.
    apply sum_Rle.
    intros n H7.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x_general mal init A) 0) = 
         (size (incl_neigh_minus_extremes i (x_general mal init A) 0) - 1).+1).
         {rewrite subn1 prednK.
         -- by [].
         -- apply size_incl_not_0_general.
         }
         rewrite H8 ltnS.
         by apply /leP.
    * unfold m_general.
      assert(exists (j1:D), j1 \in
      (inclusive_neighbor_list i) /\ j1 \in Normal_general A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x_general mal init A) 0) ->
      ((x_general mal init A 0 j1) <= (x_general mal init A 0 k))%Re).
      {by apply exists_j1_general. }
      elim H8.
      intros v H9.
      destruct H9. destruct H10.
      rewrite -mem_enum in H10.
      apply Rle_trans with (r2:= (x_general mal init A 0 v)).
      ++ remember [seq (- x_general mal init A 0 i) | i <- enum (Normal_general A)] as x_incl.
         remember [seq (x_general mal init A 0 i) | i <- enum (Normal_general A)] as pos_x_incl.
         rewrite <- nth_index with (x0:=0) (x:= (x_general mal init A 0 v))
         (s:=pos_x_incl).
         -- assert(pos_x_incl`_(index ((x_general mal init A 0 v)) pos_x_incl) =
            - - pos_x_incl`_(index ((x_general mal init A 0 v)) pos_x_incl))%Re.
            {by rewrite Ropp_involutive. }
            rewrite H12.
            apply Ropp_le_contravar.
            assert(- pos_x_incl`_(index (x_general mal init A 0 v) pos_x_incl) =
            x_incl`_(index (- (x_general mal init A 0 v)) x_incl))%Re.
            {rewrite nth_index.
            ** rewrite nth_index.
               +++ by [].
               +++ rewrite Heqx_incl.
                   apply /mapP.
                   by exists v.
            ** rewrite Heqpos_x_incl.
               apply /mapP.
               by exists v.
            }
            rewrite H13.
            apply /RlebP.
            apply bigmaxr_ler with (x0:=0) (s:= x_incl)
            (i0:=(index (- (x_general mal init A 0 v)) x_incl)).
            rewrite Heqx_incl index_mem.
            apply /mapP. by exists v.
         -- rewrite Heqpos_x_incl.
            apply /mapP. by exists v.
      ++ apply H11, mem_nth.
         assert((n <= size (incl_neigh_minus_extremes i (x_general mal init A) 0) - 1)%N).
         {by apply /leP. }
         rewrite subn1 -ltnS prednK in H12.
         -- by [].
         -- rewrite -has_predT.
            apply /hasP.
            exists i.
            ** apply i_in_incl_general.
            ** by [].
    * by [].
  - rewrite /= H2.
    assert(aux1: i \in Normal_general A). {by []. }
    assert(aux2: wts_well_behaved_general A mal init). {by []. }
    rewrite /wts_well_behaved_general in H0.
    destruct H0 as [a H0]. destruct H0. destruct H3.
    specialize (H4 (t'.+1)%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig_general with
    (mal:=mal) (init:=init) (A:=A) (r:=(m_general mal init A t'.+1)) (i:=i) (t:=t'.+1%N).
    rewrite -addnE addn1.
    apply sum_Rle.
    intros n H7.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x_general mal init A) (t'.+1)) = 
         (size (incl_neigh_minus_extremes i (x_general mal init A) (t'.+1)) - 1).+1).
         {rewrite subn1 prednK.
         -- by [].
         -- apply size_incl_not_0_general.
         }
         rewrite H8 ltnS.
         by apply /leP.
    * assert(exists (j1:D), j1 \in
      (inclusive_neighbor_list i) /\ j1 \in Normal_general A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x_general mal init A) t'.+1) ->
      ((x_general mal init A t'.+1 j1) <= (x_general mal init A t'.+1 k))%Re).
      {by apply exists_j1_general. }
      elim H8.
      intros v H9.
      destruct H9. destruct H10.
      rewrite -mem_enum in H10.
      apply Rle_trans with (r2:= (x_general mal init A (t'.+1) v)).
      ++ remember [seq (- x_general mal init A t'.+1 i) | i <- enum (Normal_general A)] as x_incl.
         remember [seq (x_general mal init A t'.+1 i) | i <- enum (Normal_general A)] as pos_x_incl.
         rewrite <- nth_index with (x0:=0) (x:= (x_general mal init A t'.+1 v))
         (s:=pos_x_incl).
         -- assert(pos_x_incl`_(index ((x_general mal init A t'.+1 v)) pos_x_incl) =
            - - pos_x_incl`_(index ((x_general mal init A t'.+1 v)) pos_x_incl))%Re.
            {by rewrite Ropp_involutive. }
            rewrite H12.
            apply Ropp_le_contravar.
            assert(- pos_x_incl`_(index (x_general mal init A t'.+1 v) pos_x_incl) =
            x_incl`_(index (- (x_general mal init A t'.+1 v)) x_incl))%Re.
            {rewrite nth_index.
            ** rewrite nth_index.
               +++ by [].
               +++ rewrite Heqx_incl.
                   apply /mapP.
                   by exists v.
            ** rewrite Heqpos_x_incl.
               apply /mapP.
               by exists v.
            }
            rewrite H13 -Heqx_incl.
            apply /RlebP.
            apply bigmaxr_ler with (x0:=0) (s:= x_incl)
            (i0:=(index (- (x_general mal init A t'.+1 v)) x_incl)).
            rewrite Heqx_incl index_mem.
            apply /mapP. by exists v.
         -- rewrite Heqpos_x_incl.
            apply /mapP. by exists v.
      ++ apply H11, mem_nth.
         assert((n <= size (incl_neigh_minus_extremes i (x_general mal init A) t'.+1) - 1)%N).
         {by apply /leP. }
         rewrite subn1 -ltnS prednK in H12.
         -- by [].
         -- rewrite -has_predT.
            apply /hasP.
            exists i.
            ** apply i_in_incl_general.
            ** by [].
    * by [].
Qed.
