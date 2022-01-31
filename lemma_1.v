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

Lemma Rle_dec_compat_Rle:
forall (r1 r2:R),
Rle_dec r1 r2 <-> (r1 <= r2)%Re.
Proof.
intros. destruct Rle_dec.
+ by split.
+ by split.
Qed.

Lemma Rlt_dec_compat_Rlt:
forall (r1 r2:R),
Rlt_dec r1 r2 <-> (r1 < r2)%Re.
Proof.
intros. destruct Rlt_dec.
+ by split.
+ by split.
Qed.

Lemma Req_dec_compat_Req:
forall (r1 r2:R),
r1 == r2 = true <-> (r1 = r2)%Re.
Proof.
intros. destruct (r1 == r2) eqn:E.
+ assert(r1 = r2)%Re. {by apply/eqP. } by [].
+ split.
  - by [].
  - intro. assert(r2 == r2). {by []. } by rewrite H H0 in E.
Qed.

Lemma Req_dec_compat_Req_1:
forall (r1 r2:R),
r1 == r2 <-> (r1 = r2)%Re.
Proof.
intros. destruct (r1 == r2) eqn:E.
+ assert(r1 = r2)%Re. {by apply/eqP. } by [].
+ split.
  - by [].
  - intro. assert(r2 == r2). {by []. } by rewrite H H0 in E.
Qed.

Lemma sorted_Dseq_rel_refl:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
sorted_Dseq_rel (x mal init A w t) i i.
Proof.
intros. unfold sorted_Dseq_rel. destruct Rle_dec.
+ by rewrite /= eq_refl leq_eqVlt eq_refl /=.
+ simpl. by apply Rnot_le_lt, Rlt_not_eq in n.
Qed.

Lemma sorted_Dseq_rel_transitive:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat),
transitive (sorted_Dseq_rel (x mal init A w t)).
Proof.
intros. unfold transitive. intros b a c. unfold sorted_Dseq_rel.
intros.
destruct (Rle_dec (x mal init A w t a) (x mal init A w t c)).
+ simpl. destruct (x mal init A w t a == x mal init A w t c) eqn:E.
  - rewrite -> Req_dec_compat_Req in E.
    destruct (index a (enum D) <= index c (enum D))%N eqn:E0.
    * by rewrite E0.
    * destruct Rle_dec.
      ++ simpl in H. destruct Rle_dec.
         -- simpl in H0.
            assert(x mal init A w t b = x mal init A w t c).
            {rewrite -E. apply Rle_antisym.
            + apply Rle_trans with (r2:=(x mal init A w t c)).
              - by [].
              - rewrite E. by right.
            + by [].
            }
            rewrite H1 eq_refl in H0.
            rewrite E H1 eq_refl in H.
            assert((index a (enum D) <= index c (enum D))%N).
            {by apply leq_trans with (n:=(index b (enum D))). }
            by rewrite H2 in E0.
         -- by simpl in H0.
      ++ by simpl in H.
  - by [].
+ simpl. destruct Rle_dec.
  - simpl in H. destruct r.
    * destruct Rle_dec.
      ++ simpl in H0.
         assert(x mal init A w t a < x mal init A w t a)%Re.
         {apply Rlt_trans with (r2:=(x mal init A w t b)).
         + by destruct r.
         + apply Rlt_trans with (r2:=(x mal init A w t c)).
           - destruct r.
             * by [].
             * rewrite -H2 in n. by apply Rnot_le_lt, Rlt_le, Rle_not_lt in n.
           - by apply Rnot_le_gt.
         }
         by apply Rlt_not_eq in H2.
      ++ by simpl in H0.
    * rewrite H1 eq_refl in H. destruct Rle_dec.
      ++ simpl in H0. by rewrite -H1 in r.
      ++ by simpl in H0.
  - by simpl in H.
Qed.

Lemma sorted_Dseq_rel_antisym:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat),
antisymmetric (sorted_Dseq_rel (x mal init A w t)).
Proof.
intros. unfold antisymmetric. intros a b. intro.
assert(sorted_Dseq_rel (x mal init A w t) a b).
{by destruct (sorted_Dseq_rel (x mal init A w t) a b). }
assert(sorted_Dseq_rel (x mal init A w t) b a).
{destruct (sorted_Dseq_rel (x mal init A w t) b a).
+ by [].
+ by rewrite andb_false_r in H.
}
clear H. unfold sorted_Dseq_rel in H0, H1.
destruct Rle_dec.
+ simpl in H0. destruct Rle_dec.
  - simpl in H1.
    assert(x mal init A w t a = x mal init A w t b)%Re.
    {by apply Rle_antisym. }
    rewrite H eq_refl in H0, H1.
    assert(index a (enum D) = index b (enum D))%N.
    {apply /eqP. rewrite eqn_leq. by rewrite H0 H1. }
    assert(nth a (enum D) (index a (enum D)) = a).
    {apply nth_index. by rewrite mem_enum. }
    assert(nth a (enum D) (index b (enum D)) = b).
    {apply nth_index. by rewrite mem_enum. }
    by rewrite -H2 H3 in H4.
  - by simpl in H1.
+ by simpl in H0.
Qed.

Lemma sorted_Dseq_rel_total:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
total (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j).
Proof.
intros. unfold total, sorted_Dseq_rel. intros a b.
destruct Rle_dec.
+ simpl. destruct r.
  - assert(x mal init A w t a == x mal init A w t b = false).
    {destruct(x mal init A w t a == x mal init A w t b) eqn:E.
    + rewrite -> Req_dec_compat_Req in E. rewrite E in H.
      by apply Rlt_not_eq in H.
    + by [].
    }
    by rewrite H0 /=.
  - rewrite H eq_refl.
    assert(Rle_dec (x mal init A w t b) (x mal init A w t b)).
    {destruct Rle_dec.
    + by [].
    + simpl. by apply Rnot_le_gt, Rgt_not_eq in n.
    }
    rewrite H0. destruct (index a (enum D) <= index b (enum D))%N eqn:E.
    * by rewrite E /=.
    * rewrite E /=. apply ltnW. by rewrite ltnNge E /=.
+ simpl.
  assert(Rle_dec (x mal init A w t b) (x mal init A w t a)).
  {destruct Rle_dec.
  + by [].
  + simpl. by apply Rnot_le_gt, Rlt_le in n.
  }
  assert(x mal init A w t b == x mal init A w t a = false).
  {destruct Rle_dec.
  + simpl in H. destruct (x mal init A w t b == x mal init A w t a) eqn:E.
    - rewrite -> Req_dec_compat_Req in E. rewrite E in n.
      by apply Rnot_le_gt, Rgt_not_eq in n.
    - by [].
  + by [].
  }
  by rewrite H H0.
Qed.

Lemma sorted_seqD_compat:
forall (l:seq D), uniq l ->
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat),
sorted (sorted_Dseq_rel (x mal init A w t)) l <->
(forall (a b:D),
a \in l -> b \in l ->
(index a l < index b l)%N ->
(sorted_Dseq_rel (x mal init A w t) a b)).
Proof.
intros l G.
split.
+ intros. apply sorted_ltn_index in H.
  - unfold prop_in2 in H. specialize (H a b). by apply H in H0.
  - apply sorted_Dseq_rel_transitive.
+ intros. destruct l as [|hd tl].
  - by [].
  - simpl. apply /(pathP hd). intros n H0. apply H.
    * apply mem_nth. simpl. by apply ltn_trans with (n:=(size tl)).
    * assert(nth hd tl n = nth hd (hd::tl) n.+1). {by []. }
      rewrite H1. apply mem_nth. rewrite /=.
      assert((n.+1 < (size tl).+1)%N =
      (n + 1 < (size tl) + 1)%N). {by rewrite !addn1. }
      by rewrite H2 ltn_add2r.
    * assert(aux: (n < (size tl))%N). {by []. }
      rewrite index_uniq.
      ++ apply (mem_nth hd) in H0.
         rewrite cons_uniq in G.
         assert(hd \in tl = false).
         {destruct (hd \in tl) eqn:E.
         + by rewrite E in G.
         + by [].
         }
         assert(hd == nth hd tl n = false).
         {destruct (hd == nth hd tl n) eqn:E.
         + assert(hd = nth hd tl n). {by apply /eqP. }
           by rewrite H2 H0 in H1.
         + by [].
         }
         rewrite /= H2. assert(uniq tl).
         {destruct (uniq tl).
         + by [].
         + by rewrite andb_false_r in G.
         }
         assert((index (nth hd tl n) tl) = n)%N.
         {by apply index_uniq. }
         rewrite H4. apply ltnSn.
      ++ simpl. by apply ltn_trans with (n:=(size tl)).
      ++ by [].
Qed.

Lemma orb_triple_simpl:
forall (b1 b2 b3:bool), [|| b1, b2 | b3] = b1 || b2 || b3.
Proof.
intros.
destruct b1.
+ by [].
+ destruct b2.
  - by [].
  - by destruct b3.
Qed.

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

Lemma inclusive_neighbors_uniq:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
uniq (inclusive_neighbor_list i (x mal init A w t)).
Proof.
intros.
assert(uniq (inclusive_neighbor_list i (x mal init A w t)) =
uniq (enum (inclusive_neigh i))).
{apply perm_uniq, permEl. apply perm_sort. }
assert(uniq (enum (inclusive_neigh i))).
{by apply enum_uniq. }
by rewrite H0 in H.
Qed.

Lemma incl_uniq:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  uniq (incl_neigh_minus_extremes i (x mal init A w t)).
Proof.
intros. apply filter_uniq, inclusive_neighbors_uniq.
Qed.

Lemma R_i_gt_mnn_subset_R_i_gt:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \notin (R_i_greater_than_maybe_not_neighbors mal init A w i t) ->
  j \notin (R_i_greater_than mal init A w i t).
Proof.
intros.
rewrite inE.
rewrite inE in H.
destruct (j \in inclusive_neighbor_list i (x mal init A w t)) eqn:E.
+ by rewrite andb_true_r.
+ by rewrite andb_false_r.
Qed.

Lemma R_i_lt_mnn_subset_R_i_lt:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \notin (R_i_less_than_maybe_not_neighbors mal init A w i t) ->
  j \notin (R_i_less_than mal init A w i t).
Proof.
intros.
rewrite inE.
rewrite inE in H.
destruct (j \in inclusive_neighbor_list i (x mal init A w t)) eqn:E.
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

Lemma R_i_lt_and_incl_disjoint:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
  j \notin R_i_less_than mal init A w i t.
Proof.
intros.
rewrite mem_filter in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rlt_Rge -leqNgt.
apply /orP.
by apply andb_triple_inject_left in H.
Qed.

Lemma R_i_gt_and_incl_disjoint:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
  j \notin R_i_greater_than mal init A w i t.
Proof.
intros.
rewrite mem_filter in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rgt_Rle -leqNgt.
apply /orP.
by apply andb_triple_inject_middle in H.
Qed.

Lemma R_i_gt_R_i_lt_disjoint:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in R_i_less_than mal init A w i t ->
  j \notin R_i_greater_than mal init A w i t.
Proof.
intros.
rewrite in_set in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rgt_Rle -leqNgt.
apply /orP.
assert(Rle_dec (x mal init A w t j) (x mal init A w t i)).
{destruct Rle_dec.
+ by [].
+ destruct Rlt_dec.
  - simpl in H. by apply Rlt_le in r.
  - by simpl in H.
}
by rewrite H1 /=.
Qed.

Lemma R_i_lt_R_i_gt_disjoint:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in R_i_greater_than mal init A w i t ->
  j \notin R_i_less_than mal init A w i t.
Proof.
intros.
rewrite in_set in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rlt_Rge -leqNgt.
apply /orP.
assert(Rge_dec (x mal init A w t j) (x mal init A w t i)).
{destruct Rge_dec.
+ by [].
+ destruct Rgt_dec.
  - simpl in H. by apply Rgt_ge in r.
  - by simpl in H.
}
by rewrite H1 /=.
Qed.

Lemma R_i_lt_and_incl_disjoint_0:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
  j \in R_i_less_than mal init A w i t = false.
Proof.
intros.
rewrite mem_filter in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rlt_Rge -leqNgt.
apply /orP.
by apply andb_triple_inject_left in H.
Qed.

Lemma R_i_gt_and_incl_disjoint_0:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
  j \in R_i_greater_than mal init A w i t = false.
Proof.
intros.
rewrite mem_filter in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rgt_Rle -leqNgt.
apply /orP.
by apply andb_triple_inject_middle in H.
Qed.

Lemma R_i_gt_R_i_lt_disjoint_0:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in R_i_less_than mal init A w i t ->
  j \in R_i_greater_than mal init A w i t = false.
Proof.
intros.
rewrite in_set in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rgt_Rle -leqNgt.
apply /orP.
assert(Rle_dec (x mal init A w t j) (x mal init A w t i)).
{destruct Rle_dec.
+ by [].
+ destruct Rlt_dec.
  - simpl in H. by apply Rlt_le in r.
  - by simpl in H.
}
by rewrite H1 /=.
Qed.

Lemma R_i_lt_R_i_gt_disjoint_0:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in R_i_greater_than mal init A w i t ->
  j \in R_i_less_than mal init A w i t = false.
Proof.
intros.
rewrite in_set in H.
rewrite inE.
assert((j \in inclusive_neighbor_list i (x mal init A w t)) = true).
{by apply andb_triple_inject_right in H. }
rewrite H0 andb_true_r.
apply /nandP.
rewrite not_Rlt_Rge -leqNgt.
apply /orP.
assert(Rge_dec (x mal init A w t j) (x mal init A w t i)).
{destruct Rge_dec.
+ by [].
+ destruct Rgt_dec.
  - simpl in H. by apply Rgt_ge in r.
  - by simpl in H.
}
by rewrite H1 /=.
Qed.

Definition sorted_Dseq (x:D -> R) (l:seq D) :=
forall (a b:D),
a \in l -> b \in l ->
(index a l < index b l)%N ->
(x a <= x b)%Re.

Lemma sorted_Dseq_compat_sorted_Dseq_rel:
forall (l:seq D), uniq l ->
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat),
(forall (a b:D),
a \in l -> b \in l ->
(index a l < index b l)%N ->
(sorted_Dseq_rel (x mal init A w t) a b)) ->
sorted_Dseq (x mal init A w t) l.
Proof.
intros. unfold sorted_Dseq. intros. specialize (H0 a b). apply H0 in H1.
+ unfold sorted_Dseq_rel in H1. by destruct Rle_dec.
+ by [].
+ by [].
Qed.

Lemma inclusive_neighbors_sorted_0:
  forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
  sorted_Dseq (x mal init A w t) (inclusive_neighbor_list i (x mal init A w t)).
Proof.
intros. apply sorted_Dseq_compat_sorted_Dseq_rel.
+ apply inclusive_neighbors_uniq.
+ apply sorted_seqD_compat.
  - apply inclusive_neighbors_uniq.
  - by apply sort_sorted, sorted_Dseq_rel_total.
Qed.

Lemma inclusive_neighbors_sorted:
  forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
  sorted (sorted_Dseq_rel (x mal init A w t)) (inclusive_neighbor_list i (x mal init A w t)).
Proof.
intros. unfold inclusive_neighbor_list.
by apply sort_sorted, sorted_Dseq_rel_total.
Qed.

Lemma incl_sorted:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
sorted_Dseq (x mal init A w t) (incl_neigh_minus_extremes i (x mal init A w t)).
Proof.
intros.
unfold sorted_Dseq. apply sorted_Dseq_compat_sorted_Dseq_rel.
+ apply incl_uniq.
+ apply sorted_seqD_compat.
  - apply incl_uniq.
  - unfold incl_neigh_minus_extremes. apply sorted_filter.
    - apply sorted_Dseq_rel_transitive.
    - by apply sort_sorted, sorted_Dseq_rel_total.
Qed.

Lemma incl_sorted_0:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D) (a b:D),
a \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
b \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
(index a (incl_neigh_minus_extremes i (x mal init A w t)) <
index b (incl_neigh_minus_extremes i (x mal init A w t)))%N ->
(x mal init A w t a <= x mal init A w t b)%Re.
Proof.
intros mal init A w t i.
assert(sorted_Dseq (x mal init A w t) (incl_neigh_minus_extremes i (x mal init A w t))).
{by apply incl_sorted. }
by unfold sorted_Dseq in H.
Qed.

Lemma incl_sorted_1:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
sorted (sorted_Dseq_rel (x mal init A w t)) (incl_neigh_minus_extremes i (x mal init A w t)).
Proof.
intros. unfold incl_neigh_minus_extremes, remove_extremes.
apply sorted_filter.
+ apply sorted_Dseq_rel_transitive.
+ apply inclusive_neighbors_sorted.
Qed.

Lemma incl_subseq_inclusive_neighbors:
  forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i:D),
subseq (incl_neigh_minus_extremes i (x mal init A w t))
(inclusive_neighbor_list i (x mal init A w t)).
Proof.
intros. apply filter_subseq.
Qed.

Lemma incl_subset_inclusive_neighbors:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
  j \in inclusive_neighbor_list i (x mal init A w t).
Proof.
intros. rewrite mem_filter in H. by apply andb_triple_inject_right in H.
Qed.

Lemma nandb:
forall (b1 b2:bool), ~~ (b1 && b2) = ~~ b1 || ~~ b2.
Proof.
intros. apply /nandP. destruct b1 eqn:E.
+ destruct b2 eqn:E0.
  - simpl. unfold not. intros. by destruct H.
  - by right.
+ by left.
Qed.

Lemma incl_set_version:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  (incl_neigh_minus_extremes i (x mal init A w t)) =
  filter (fun (j:D) =>
  (j \notin (R_i_less_than_maybe_not_neighbors mal init A w i t)) &&
  (j \notin (R_i_greater_than_maybe_not_neighbors mal init A w i t)))
  (inclusive_neighbor_list i (x mal init A w t)).
Proof.
intros. unfold incl_neigh_minus_extremes.
apply eq_filter.
unfold eqfun.
intro v.
by rewrite !inE !nandb -!leqNgt not_Rlt_Rge not_Rgt_Rle.
Qed.

Lemma i_in_inclusive_neighbors:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  i \in (inclusive_neighbor_list i (x mal init A w t)).
Proof.
intros.
unfold inclusive_neighbor_list.
assert(sort (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)
(enum (inclusive_neigh i)) =i (enum (inclusive_neigh i))).
{apply perm_mem, permEl, perm_sort. }
rewrite H.
rewrite unfold_in /= -inE set_enum.
apply set1Ur.
Qed.

Lemma i_in_incl:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  i \in (incl_neigh_minus_extremes i (x mal init A w t)).
Proof.
intros.
rewrite mem_filter.
destruct Rge_dec.
+ destruct Rle_dec.
  - simpl. by apply i_in_inclusive_neighbors.
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

Lemma incl_not_empty:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  (incl_neigh_minus_extremes i (x mal init A w t)) != [::].
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
unfold negb.
destruct (incl == [::]) eqn:E.
+ assert((0 < size incl)%N).
  {apply leq_ltn_trans with (n:=index i incl).
  + apply leq0n.
  + rewrite index_mem Heqincl. apply i_in_incl.
  }
  rewrite -size_eq0 in E.
  assert(size incl = 0%N). {by apply /eqP. }
  by rewrite H0 in H.
+ by [].
Qed.

Lemma inclusive_neighbors_split:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R) (t:nat) (i j:D),
j \in inclusive_neighbor_list i (x mal init A w t) =
(j \in R_i_less_than mal init A w i t) ||
(j \in incl_neigh_minus_extremes i (x mal init A w t)) ||
(j \in R_i_greater_than mal init A w i t).
Proof.
intros. destruct (j \in R_i_less_than mal init A w i t) eqn:E.
+ simpl. rewrite in_set in E. by apply andb_triple_inject_right in E.
+ simpl. destruct (j \in R_i_greater_than mal init A w i t) eqn:E0.
  - rewrite orb_true_r. rewrite in_set in E0.
    by apply andb_triple_inject_right in E0.
  - rewrite orb_false_r incl_set_version mem_filter.
    destruct (j \in inclusive_neighbor_list i (x mal init A w t)) eqn:E1.
    * rewrite E1 andb_true_r. symmetry. apply /andP. split.
      ++ rewrite in_set E1 andb_true_r in E. by rewrite inE E.
      ++ rewrite in_set E1 andb_true_r in E0. by rewrite inE E0.
    * by rewrite E1 andb_false_r.
Qed.

Lemma merges_sorted:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
sorted (sorted_Dseq_rel (x mal init A w t))
(merge (sorted_Dseq_rel (x mal init A w t)) (sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_less_than mal init A w i t)))
(merge (sorted_Dseq_rel (x mal init A w t)) (incl_neigh_minus_extremes i (x mal init A w t))
(sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_greater_than mal init A w i t))))).
Proof.
intros.
apply merge_sorted.
+ by apply sorted_Dseq_rel_total.
+ by apply sort_sorted, sorted_Dseq_rel_total.
+ apply merge_sorted.
  - by apply sorted_Dseq_rel_total.
  - apply incl_sorted_1.
  - by apply sort_sorted, sorted_Dseq_rel_total.
Qed.

Lemma my_allrel_merge:
forall (T:Type) (s1 s2: seq T) (leT: rel T),
allrel leT s1 s2 -> merge leT s1 s2 = s1 ++ s2.
Proof.
intros T s1 s2 leT.
elim: s1 s2 => [|x s1 IHs1] [|y s2]; rewrite ?cats0 //=.
by rewrite allrel_consl /= -andbA => /and3P [-> _ /IHs1->].
Qed.

Lemma merges_eq_cats:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
(merge (sorted_Dseq_rel (x mal init A w t)) (sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_less_than mal init A w i t)))
(merge (sorted_Dseq_rel (x mal init A w t)) (incl_neigh_minus_extremes i (x mal init A w t))
(sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_greater_than mal init A w i t))))) =
(sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_less_than mal init A w i t))) ++
(incl_neigh_minus_extremes i (x mal init A w t)) ++
(sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_greater_than mal init A w i t))).
Proof.
intros.
assert(allrel
(fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)
(incl_neigh_minus_extremes i (x mal init A w t))
(sort (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)
(enum (R_i_greater_than mal init A w i t)))).
{unfold allrel. apply /allP. unfold prop_in1. intros j H.
simpl. apply /allP. unfold prop_in1. intros k H0.
unfold sorted_Dseq_rel.
assert(sorted (sorted_Dseq_rel (x mal init A w t)) (sort
(fun i j : D => sorted_Dseq_rel (x mal init A w t) i j)
(enum (R_i_greater_than mal init A w i t)))).
{by apply sort_sorted, sorted_Dseq_rel_total. }
assert(k \in R_i_greater_than mal init A w i t).
{by rewrite mem_sort mem_enum in H0. }
assert(k \in (inclusive_neighbor_list i (x mal init A w t))).
{rewrite in_set in H2. by apply andb_triple_inject_right in H2. }
assert(j \in (inclusive_neighbor_list i (x mal init A w t))).
{rewrite mem_filter in H. by apply andb_triple_inject_right in H. }
destruct (index j (inclusive_neighbor_list i (x mal init A w t)) <
index k (inclusive_neighbor_list i (x mal init A w t)))%N eqn:E.
+ assert(sorted (sorted_Dseq_rel (x mal init A w t))
  (inclusive_neighbor_list i (x mal init A w t))).
  {apply inclusive_neighbors_sorted. }
  apply sorted_ltn_index in H5. unfold prop_in2 in H5.
  specialize (H5 j k). apply H5 in H4.
  - by unfold sorted_Dseq_rel in H4.
  - by [].
  - by [].
  - apply sorted_Dseq_rel_transitive.
+ assert(index k (inclusive_neighbor_list i (x mal init A w t)) <=
  index j (inclusive_neighbor_list i (x mal init A w t)))%N.
  {by rewrite leqNgt E. }
  rewrite leq_eqVlt in H5.
  destruct (index k (inclusive_neighbor_list i (x mal init A w t)) ==
  index j (inclusive_neighbor_list i (x mal init A w t))) eqn:E0.
  - assert((index k (inclusive_neighbor_list i (x mal init A w t)) =
    index j (inclusive_neighbor_list i (x mal init A w t)))).
    {by apply /eqP. }
    assert(k = j).
    {assert(nth i (inclusive_neighbor_list i (x mal init A w t))
    (index k (inclusive_neighbor_list i (x mal init A w t))) = k).
    {by apply nth_index. }
    assert(nth i (inclusive_neighbor_list i (x mal init A w t))
    (index j (inclusive_neighbor_list i (x mal init A w t))) = j).
    {by apply nth_index. }
    by rewrite -H6 H7 in H8.
    }
    rewrite H7. destruct Rle_dec.
    * by rewrite /= eq_refl leq_eqVlt eq_refl /=.
    * simpl. by apply Rnot_le_lt, Rlt_not_eq in n.
  - simpl in H4.
    rewrite in_set H3 andb_true_r in H2.
    rewrite mem_filter H4 andb_true_r in H.
    destruct Rge_dec.
    * simpl in H. destruct Rle_dec.
      ++ assert((x mal init A w t j) = (x mal init A w t i))%Re.
         {apply Rge_le in r. by apply Rle_antisym. }
         rewrite H6. destruct Rle_dec.
         -- destruct Rgt_dec.
            ** assert(x mal init A w t i == x mal init A w t k = false).
               {destruct (x mal init A w t i == x mal init A w t k) eqn:E1.
               + rewrite -> Req_dec_compat_Req in E1. simpl in H2.
                 rewrite E1 in r2. by apply Rgt_not_eq in r2.
               + by [].
               }
               by rewrite /= H7.
            ** by simpl in H2.
         -- destruct Rgt_dec.
            ** simpl in H2. by apply Rgt_lt, Rlt_le in r1.
            ** by simpl in H4.
      ++ simpl in H.
         assert((index j (inclusive_neighbor_list i (x mal init A w t)) <=
         index k (inclusive_neighbor_list i (x mal init A w t)))%N).
         {apply leq_trans with (n:=(size (inclusive_neighbor_list i (x mal init A w t)) - F - 1)%N).
         + by [].
         + apply ltnW.
           destruct ((size (inclusive_neighbor_list i (x mal init A w t)) - F - 1 <
           index k (inclusive_neighbor_list i (x mal init A w t)))%N).
           - by [].
           - by rewrite andb_false_r in H2.
         }
         apply leq_gtF in H6. by rewrite H6 in H5.
    * simpl in H. apply Rnot_ge_gt, Rgt_lt, Rlt_le in n.
      assert((x mal init A w t j) <= (x mal init A w t k))%Re.
      {apply Rle_trans with (r2:=(x mal init A w t i)%Re).
      + by [].
      + destruct Rgt_dec.
        - simpl in H2. apply Rgt_lt in r. by left.
        - by simpl in H2.
      }
      assert(Rle_dec (x mal init A w t j) (x mal init A w t k)).
      {by destruct (Rle_dec (x mal init A w t j) (x mal init A w t k)). }
      assert((x mal init A w t j) == (x mal init A w t k) = false).
      {destruct (x mal init A w t j == x mal init A w t k) eqn:E1.
      + rewrite -> Req_dec_compat_Req in E1. rewrite E1 in n.
        destruct Rgt_dec.
        - simpl in H2. by apply Rgt_not_le in r.
        - by simpl in H2.
      + by [].
      }
      by rewrite H7 H8.
}
rewrite !my_allrel_merge.
+ by [].
+ by [].
+ clear H. unfold allrel. apply /allP. unfold prop_in1. intros j H.
  simpl. apply /allP. unfold prop_in1. intros k H0.
  rewrite mem_cat in H0.
  destruct(k \in incl_neigh_minus_extremes i (x mal init A w t)) eqn:Eincl.
  - clear H0.
    assert(sorted (sorted_Dseq_rel (x mal init A w t))
    (sort (fun i j : D => sorted_Dseq_rel (x mal init A w t) i j)
    (enum (R_i_less_than mal init A w i t)))).
    {by apply sort_sorted, sorted_Dseq_rel_total. }
    assert(j \in R_i_less_than mal init A w i t).
    {by rewrite mem_sort mem_enum in H. }
    assert(j \in (inclusive_neighbor_list i (x mal init A w t))).
    {rewrite in_set in H1. by apply andb_triple_inject_right in H1. }
    assert(k \in (inclusive_neighbor_list i (x mal init A w t))).
    {rewrite mem_filter in Eincl. by apply andb_triple_inject_right in Eincl. }
    destruct (index j (inclusive_neighbor_list i (x mal init A w t)) <
    index k (inclusive_neighbor_list i (x mal init A w t)))%N eqn:E.
    * assert(sorted (sorted_Dseq_rel (x mal init A w t))
      (inclusive_neighbor_list i (x mal init A w t))).
      {apply inclusive_neighbors_sorted. }
      apply sorted_ltn_index in H4.
      ++ unfold prop_in2 in H4. specialize (H4 j k). by apply H4.
      ++ apply sorted_Dseq_rel_transitive.
    * assert(index k (inclusive_neighbor_list i (x mal init A w t)) <=
      index j (inclusive_neighbor_list i (x mal init A w t)))%N.
      {by rewrite leqNgt E. }
      destruct (index k (inclusive_neighbor_list i (x mal init A w t)) ==
      index j (inclusive_neighbor_list i (x mal init A w t))) eqn:E0.
      ++ assert((index k (inclusive_neighbor_list i (x mal init A w t)) =
         index j (inclusive_neighbor_list i (x mal init A w t)))).
         {by apply /eqP. }
         assert(k = j).
         {assert(nth i (inclusive_neighbor_list i (x mal init A w t))
         (index k (inclusive_neighbor_list i (x mal init A w t))) = k).
         {by apply nth_index. }
         assert(nth i (inclusive_neighbor_list i (x mal init A w t))
         (index j (inclusive_neighbor_list i (x mal init A w t))) = j).
         {by apply nth_index. }
         by rewrite -H5 H6 in H7.
         }
         rewrite H6. apply sorted_Dseq_rel_refl.
      ++ simpl in H4.
         rewrite in_set H2 andb_true_r in H1.
         rewrite mem_filter H3 andb_true_r in Eincl.
         destruct Rle_dec.
         -- rewrite andb_true_r in Eincl. destruct Rge_dec.
            ** assert((x mal init A w t k) = (x mal init A w t i))%Re.
               {simpl in Eincl. apply Rge_le in r0. by apply Rle_antisym. }
               unfold sorted_Dseq_rel. rewrite H5. destruct Rle_dec.
               +++ simpl. destruct Rlt_dec.
                   --- assert(x mal init A w t j == x mal init A w t i = false).
                       {destruct (x mal init A w t j == x mal init A w t i) eqn:E1.
                       + simpl in H1. rewrite -> Req_dec_compat_Req in E1.
                         rewrite E1 in r2. by apply Rlt_not_eq in r2.
                       + by [].
                       }
                       by rewrite H6.
                   --- by simpl in H1.
               +++ destruct Rlt_dec.
                   --- simpl in H1. by apply Rgt_lt, Rlt_le in r1.
                   --- by simpl in H3.
            ** simpl in Eincl.
               assert((index j (inclusive_neighbor_list i (x mal init A w t)) <=
               index k (inclusive_neighbor_list i (x mal init A w t)))%N).
               {apply leq_trans with (n:= F).
               + assert((index j (inclusive_neighbor_list i (x mal init A w t)) < F)%N).
                 {destruct (index j (inclusive_neighbor_list i (x mal init A w t)) < F)%N.
                 + by [].
                 + by rewrite andb_false_r in H1.
                 }
                 by rewrite leq_eqVlt H5 orb_true_r.
               + by [].
               }
               apply leq_gtF in H5. by rewrite leq_eqVlt E0 H5 in H4.
         -- simpl in Eincl. apply Rnot_le_lt, Rlt_gt, Rgt_ge in n.
            assert((x mal init A w t j) <= (x mal init A w t k))%Re.
            {apply Rle_trans with (r2:=(x mal init A w t i)%Re).
            + destruct Rlt_dec.
              - by left.
              - by simpl in H1.
            + by apply Rge_le.
            }
            unfold sorted_Dseq_rel. destruct Rle_dec.
            ** simpl. destruct (x mal init A w t j == x mal init A w t k) eqn:E1.
               +++ rewrite -> Req_dec_compat_Req in E1.
                   rewrite E1 in H1. destruct Rlt_dec.
                   --- simpl in H1. by apply Rlt_not_ge in r0.
                   --- by simpl in H1.
               +++ by [].
            ** by [].
  - rewrite /= mem_sort mem_enum in H0.
    rewrite mem_sort mem_enum in H. unfold sorted_Dseq_rel.
    assert((x mal init A w t j) < (x mal init A w t k))%Re.
    {apply Rlt_trans with (r2:=(x mal init A w t i)).
    + rewrite in_set in H. apply andb_triple_inject_left in H.
      by destruct Rlt_dec.
    + rewrite in_set in H0. apply andb_triple_inject_left in H0.
      by destruct Rgt_dec.
    }
    assert(Rle_dec (x mal init A w t j) (x mal init A w t k)).
    {destruct Rle_dec.
    + by [].
    + simpl in H1. by apply Rlt_le in H1.
    }
    rewrite H2.
    assert(x mal init A w t j == x mal init A w t k = false).
    {destruct(x mal init A w t j == x mal init A w t k) eqn:E.
    + rewrite -> Req_dec_compat_Req in E. rewrite E in H1.
      by apply Rlt_not_eq in H1.
    + by [].
    }
    by rewrite H3.
+ by [].
Qed.

Lemma partition_incl:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
inclusive_neighbor_list i (x mal init A w t) =
(sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_less_than mal init A w i t))) ++
(incl_neigh_minus_extremes i (x mal init A w t)) ++
(sort ((sorted_Dseq_rel (x mal init A w t)) )
(enum (R_i_greater_than mal init A w i t))).
Proof.
intros. rewrite -merges_eq_cats.
remember (R_i_less_than mal init A w i t) as R_i_lt.
remember (R_i_greater_than mal init A w i t) as R_i_gt.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
remember (sort (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)
  (enum R_i_lt)) as R_i_lt_sorted.
remember (sort (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)
  (enum R_i_gt)) as R_i_gt_sorted.
assert(sorted (sorted_Dseq_rel (x mal init A w t)) (merge (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)
  R_i_lt_sorted
  (merge
     (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)
     incl R_i_gt_sorted))).
{apply merge_sorted.
+ by apply sorted_Dseq_rel_total.
+ rewrite HeqR_i_lt_sorted. by apply sort_sorted, sorted_Dseq_rel_total.
+ apply merge_sorted.
  - by apply sorted_Dseq_rel_total.
  - rewrite Heqincl. apply incl_sorted_1.
  - rewrite HeqR_i_gt_sorted. by apply sort_sorted, sorted_Dseq_rel_total.
}
unfold inclusive_neighbor_list. apply sorted_sort in H.
assert(transitive (fun i0 j : D => sorted_Dseq_rel (x mal init A w t) i0 j)).
{apply sorted_Dseq_rel_transitive. }
rewrite -H.
+ apply /perm_sortP.
  - by apply sorted_Dseq_rel_total.
  - by [].
  - apply sorted_Dseq_rel_antisym.
  - rewrite Heqincl HeqR_i_lt_sorted HeqR_i_gt_sorted HeqR_i_lt HeqR_i_gt.
    rewrite merges_eq_cats. apply uniq_perm.
    * apply enum_uniq.
    * rewrite cat_uniq. apply /and3P. split.
      ++ rewrite sort_uniq. apply enum_uniq.
      ++ apply /hasPn. unfold prop_in1. intros j H1. simpl.
         rewrite mem_cat in H1.
         destruct(j \in sort (sorted_Dseq_rel (x mal init A w t))
         (enum (R_i_less_than mal init A w i t))) eqn:E.
         -- destruct (j \in incl_neigh_minus_extremes i (x mal init A w t)) eqn:E0.
            ** rewrite mem_sort mem_enum in E.
               apply R_i_lt_and_incl_disjoint in E0.
               by rewrite E in E0.
            ** rewrite /= mem_sort mem_enum in H1.
               apply R_i_lt_R_i_gt_disjoint in H1.
               rewrite mem_sort mem_enum in E.
               by rewrite E in H1.
         -- by rewrite E.
      ++ rewrite cat_uniq. apply /and3P. split.
         -- apply incl_uniq.
         -- apply /hasPn. unfold prop_in1. intros j H1. simpl.
            destruct (j \in incl_neigh_minus_extremes i (x mal init A w t)) eqn:E.
            ** apply R_i_gt_and_incl_disjoint in E.
               rewrite mem_sort mem_enum in H1.
               by rewrite H1 in E.
            ** by rewrite E.
         -- rewrite sort_uniq. apply enum_uniq.
    * unfold eq_mem. intro j. rewrite !mem_cat !mem_sort orb_triple_simpl !mem_enum.
      rewrite -inclusive_neighbors_split.
      unfold inclusive_neighbor_list. by rewrite mem_sort mem_enum.
+ apply sorted_Dseq_rel_transitive.
Qed.

Lemma last_incl_in_incl:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  let incl := (incl_neigh_minus_extremes i (x mal init A w t)) in
  (last (head i incl) (behead incl)) \in incl.
Proof.
intros. simpl.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
rewrite -> list_dissect with (l:=incl) (i:=i) at 3.
rewrite mem_last.
+ by [].
+ rewrite Heqincl.
  apply incl_not_empty.
Qed.

Lemma size_incl_not_0:
  forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  (0 < size ((incl_neigh_minus_extremes i (x mal init A w t))))%N.
Proof.
intros.
destruct (0 == size (incl_neigh_minus_extremes i (x mal init A w t)))%N eqn:E.
+ assert((0 = size (incl_neigh_minus_extremes i (x mal init A w t)))%N).
  {apply /eqP. rewrite E. by []. }
  symmetry in H. apply size0nil in H.
  assert(incl_neigh_minus_extremes i (x mal init A w t) != [::]).
  {apply incl_not_empty. }
  by rewrite H in H0.
+ rewrite lt0n.
  apply /eqP.
  unfold not.
  intros.
  by rewrite H in E.
Qed.

Lemma last_incl_is_max:
  forall (i k:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  let incl := (incl_neigh_minus_extremes i (x mal init A w t)) in
  k \in incl -> (x mal init A w t k <= x mal init A w t
  (last (head i incl) (behead incl)))%Re.
Proof.
intros.
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
+ apply incl_sorted with (i:=i) (t:=t) (mal:=mal) (init:=init) (A:=A) (w:=w).
  - by [].
  - apply last_incl_in_incl.
  - rewrite (last_nth (head i incl)) -list_dissect.
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
         + rewrite (last_nth i) -list_dissect.
           by rewrite size_behead nth_last.
         + apply (incl_not_empty i t mal init A w).
         }
         rewrite H1 in H.
         destruct (k == last (head i incl) (behead incl)) eqn:E.
         -- by [].
         -- by rewrite orb_false_r in H.
      ++ apply size_incl_not_0.
      ++ rewrite ltn_predL. apply size_incl_not_0.
      ++ rewrite ltn_predL. apply size_incl_not_0.
      ++ apply incl_uniq.
    * apply incl_not_empty.
Qed.

Lemma first_incl_is_min:
  forall (i k:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  let incl := (incl_neigh_minus_extremes i (x mal init A w t)) in
  k \in incl -> (x mal init A w t (nth i incl 0) <= x mal init A w t k)%Re.
Proof.
intros.
destruct (k == (nth i incl 0)) eqn:E.
+ assert(k = nth i incl 0).
  {by apply /eqP. }
  rewrite -H0.
  by right.
+ apply incl_sorted with (i:=i) (t:=t) (mal:=mal) (init:=init) (A:=A) (w:=w).
  - rewrite mem_nth.
    * by [].
    * apply size_incl_not_0.
  - by [].
  - rewrite index_uniq.
    * destruct (0 == index k incl)%N eqn:E0.
      ++ assert(0 = index k incl)%N.
         {by apply /eqP. }
         rewrite H0 nth_index in E.
         -- assert(k == k = true). {by apply /eqP. }
            by rewrite H1 in E.
         -- by [].
      ++ rewrite eq_sym in E0. by apply neq0_lt0n.
    * apply size_incl_not_0.
    * apply incl_uniq.
Qed.

Lemma in_R_i_gt_bounds_incl:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  j \in R_i_greater_than mal init A w i t ->
  (x mal init A w t (last (head i (incl_neigh_minus_extremes i (x mal init A w t)))
  (behead (incl_neigh_minus_extremes i (x mal init A w t)))) <= x mal init A w t j)%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
destruct ((last (head i incl) (behead incl)) \in
R_i_greater_than mal init A w i t) eqn:E.
+ assert((last (head i incl) (behead incl)) \in incl).
  {rewrite Heqincl. apply last_incl_in_incl. }
  rewrite -> Heqincl in H0 at 3.
  rewrite incl_set_version mem_filter in H0.
  apply andb_triple_inject_middle in H0.
  apply R_i_gt_mnn_subset_R_i_gt in H0.
  unfold negb in H0. by rewrite E in H0.
+ rewrite inE in E. apply andb_triple_eq_false in E.
  assert((last (head i incl) (behead incl) \in inclusive_neighbor_list i (x mal init A w t)) = true).
  {apply incl_subset_inclusive_neighbors with (t:=t) (mal:=mal) (init:=init) (A:=A) (w:=w).
  rewrite Heqincl. apply last_incl_in_incl. }
  rewrite H0 /= orb_false_r not_Rgt_Rle -leqNgt in E.
  destruct Rle_dec.
  - apply Rle_trans with (r2:=(x mal init A w t i)).
    * by [].
    * rewrite inE in H. apply andb_triple_inject_left in H.
      destruct Rgt_dec.
      ++ simpl in H. by apply Rgt_ge, Rge_le in r0.
      ++ by [].
  - simpl in E. apply inclusive_neighbors_sorted_0 with (i:=i).
    * by [].
    * rewrite in_set in H. by apply andb_triple_inject_right in H.
    * rewrite inE in H. apply andb_triple_inject_middle in H.
      by apply leq_ltn_trans with
      (n:=(size (inclusive_neighbor_list i (x mal init A w t)) - F - 1)%N).
Qed.

Lemma in_R_i_lt_bounds_incl:
forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
j \in R_i_less_than mal init A w i t ->
(x mal init A w t j <= x mal init A w t (nth i (incl_neigh_minus_extremes i (x mal init A w t)) 0))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
destruct ((nth i incl 0) \in
R_i_less_than mal init A w i t) eqn:E.
+ assert((nth i incl 0) \in incl).
  {apply mem_nth. rewrite Heqincl. apply size_incl_not_0. }
  rewrite Heqincl incl_set_version mem_filter in H0.
  apply andb_triple_inject_left, R_i_lt_mnn_subset_R_i_lt in H0.
  rewrite -incl_set_version -Heqincl in H0. by rewrite E in H0.
+ rewrite inE in E. apply andb_triple_eq_false in E.
  assert((nth i incl 0 \in inclusive_neighbor_list i (x mal init A w t)) = true).
  {apply incl_subset_inclusive_neighbors with (t:=t) (mal:=mal) (init:=init) (A:=A) (w:=w).
  rewrite Heqincl. apply mem_nth, size_incl_not_0. }
  rewrite H0 /= orb_false_r not_Rlt_Rge -leqNgt in E.
  destruct Rge_dec.
  - apply Rle_trans with (r2:=(x mal init A w t i)).
    * rewrite inE in H. apply andb_triple_inject_left in H.
      destruct Rlt_dec.
      ++ by left.
      ++ by [].
    * rewrite inE in H. apply andb_triple_inject_left in H.
      destruct Rlt_dec.
      ++ simpl in E. by apply Rge_le in r.
      ++ by [].
  - simpl in E. rewrite inE in H. rewrite Heqincl.
    apply inclusive_neighbors_sorted_0 with (t:=t) (i:=i).
    * by apply andb_triple_inject_right in H.
    * by rewrite -Heqincl.
    * apply ltn_leq_trans with (n:=F).
      ++ by apply andb_triple_inject_middle in H.
      ++ by rewrite -Heqincl.
Qed.

Lemma exists_normal_node_in_R_i_gt:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
F_total_malicious mal init A w ->
R_i_greater_than mal init A w i t != Adversary A ->
#|R_i_greater_than mal init A w i t| == F ->
(exists (j:D), (j \in (Normal A) /\
j \in R_i_greater_than mal init A w i t)).
Proof.
intros. destruct H. destruct H.
assert((exists (j:D), j \in ((Normal A) :&: (R_i_greater_than mal init A w i t))) ->
exists j : D, j \in (Normal A) /\ j \in R_i_greater_than mal init A w i t).
{intro. elim H4. intros v H5. rewrite inE in H5.
exists v. by apply /andP.
}
apply H4. apply /set0Pn.
destruct ((Normal A) :&: R_i_greater_than mal init A w i t != set0) eqn:E.
+ by [].
+ assert(Normal A :&: R_i_greater_than mal init A w i t == set0).
  {unfold negb in E.
  by destruct (Normal A :&: R_i_greater_than mal init A w i t == set0).
  }
  rewrite setIC setI_eq0 in H5.
  assert((R_i_greater_than mal init A w i t) :\: Normal A = (R_i_greater_than mal init A w i t)).
  {by apply /setDidPl. }
  unfold Normal in H6. rewrite setDDr setDT set0U in H6.
  assert((R_i_greater_than mal init A w i t) \subset Adversary A).
  {apply /setIidPr. by rewrite setIC. }
  assert(#|R_i_greater_than mal init A w i t| = F). {by apply /eqP. }
  rewrite -H8 in H3.
  assert(R_i_greater_than mal init A w i t == Adversary A).
  {rewrite eqEcard. apply /andP. by split. }
  assert(R_i_greater_than mal init A w i t = Adversary A). {by apply /eqP. }
  rewrite H10 in H0. unfold negb in H0.
  assert((Adversary A == Adversary A) = true). {by apply /eqP. }
  by rewrite H11 in H0.
Qed.

Lemma exists_normal_node_in_R_i_lt:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
F_total_malicious mal init A w ->
R_i_less_than mal init A w i t != Adversary A ->
#|R_i_less_than mal init A w i t| == F ->
(exists (j:D), (j \in Normal A /\
j \in R_i_less_than mal init A w i t)).
Proof.
intros. destruct H. destruct H.
assert((exists (j:D), j \in (Normal A :&: (R_i_less_than mal init A w i t))) ->
exists j : D, j \in Normal A /\ j \in R_i_less_than mal init A w i t).
{intro. elim H4. intros v H5. rewrite inE in H5.
exists v. by apply /andP.
}
apply H4. apply /set0Pn.
destruct (Normal A :&: R_i_less_than mal init A w i t != set0) eqn:E.
+ by [].
+ assert(Normal A :&: R_i_less_than mal init A w i t == set0).
  {unfold negb in E.
  by destruct (Normal A :&: R_i_less_than mal init A w i t == set0).
  }
  rewrite setIC setI_eq0 in H5.
  assert((R_i_less_than mal init A w i t) :\: Normal A = (R_i_less_than mal init A w i t)).
  {by apply /setDidPl. }
  rewrite setDDr setDT set0U in H6.
  assert((R_i_less_than mal init A w i t) \subset Adversary A).
  {apply /setIidPr. by rewrite setIC. }
  assert(#|R_i_less_than mal init A w i t| = F). {by apply /eqP. }
  rewrite -H8 in H3.
  assert(R_i_less_than mal init A w i t == Adversary A).
  {rewrite eqEcard. apply /andP. by split. }
  assert(R_i_less_than mal init A w i t = Adversary A). {by apply /eqP. }
  rewrite H10 in H0. unfold negb in H0.
  assert((Adversary A == Adversary A) = true). {by apply /eqP. }
  by rewrite H11 in H0.
Qed.

Lemma filter_index_drop:
forall (i:D) (n:nat) (l:seq D),
uniq l -> filter (fun (j:D) => (n <= index j l)%N) l = drop n l.
Proof.
intros i n. induction n as [|n' IHn'].
+ intro. by rewrite drop0 filter_predT.
+ intros l H. induction l as [|h t].
  - by [].
  - assert(h == h = true). {by apply /eqP. }
    assert((n' < 0)%N = false). {by rewrite ltn0. }
    rewrite /= H0 H1 -IHn'.
    assert(uniq (h :: t) = true). {by []. }
    rewrite cons_uniq in H2. apply andb_prop in H2. destruct H2.
    * apply eq_in_filter. unfold prop_in1. intros j H4.
      destruct (h == j) eqn:E.
      ++ unfold negb in H2.
         assert(h = j). {by apply /eqP. }
         rewrite -H5 in H4.
         assert((h \in t) = true). {by []. }
         by rewrite H6 in H2.
      ++ by [].
    * rewrite cons_uniq in H. apply andb_prop in H. by destruct H.
Qed.

Lemma filter_index_take:
forall (i:D) (n:nat) (l:seq D),
uniq l -> filter (fun (j:D) => (index j l < n)%N) l = take n l.
Proof.
intros i n. induction n as [|n' IHn'].
+ intro. by rewrite take0 filter_pred0.
+ intros l H. induction l as [|h t].
  - by [].
  - assert(h == h = true). {by apply /eqP. }
    assert((0 < n'.+1)%N = true). {by rewrite ltn0Sn. }
    rewrite /= H0 H1 -IHn'.
    * assert(uniq (h :: t) = true). {by []. }
      rewrite cons_uniq in H2. apply andb_prop in H2.
      destruct H2. apply /eqP.
      rewrite eqseq_cons H0 /=. apply /eqP.
      apply eq_in_filter. intros j H4.
      destruct (h == j) eqn:E.
      ++ assert(h = j). {by apply /eqP. }
         rewrite -H5 in H4.
         assert((h \in t) = true). {by []. }
         by rewrite H6 in H2.
      ++ by [].
    * assert(uniq (h :: t) = true). {by []. }
      rewrite cons_uniq in H2. apply andb_prop in H2. by destruct H2.
Qed.

Lemma index_last_incl:
  forall (t:nat) (i:D) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  (index (last (head i (incl_neigh_minus_extremes i (x mal init A w t)))
  (behead (incl_neigh_minus_extremes i (x mal init A w t)))) (inclusive_neighbor_list i (x mal init A w t)) =
  (size (inclusive_neighbor_list i (x mal init A w t)) - #|R_i_greater_than mal init A w i t| - 1))%N.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
rewrite (partition_incl i t mal init A w) !index_cat.
assert(last (head i incl) (behead incl)
\in sort (sorted_Dseq_rel (x mal init A w t))
          (enum (R_i_less_than mal init A w i t)) = false).
{rewrite mem_sort mem_enum. apply R_i_lt_and_incl_disjoint_0.
rewrite Heqincl. apply last_incl_in_incl.
}
rewrite H.
assert(last (head i incl) (behead incl)
\in incl_neigh_minus_extremes i (x mal init A w t) = true).
{rewrite -Heqincl.
assert((last (head i incl) (behead incl) \in incl)).
{rewrite Heqincl. apply last_incl_in_incl. }
by [].
}
rewrite H0 -Heqincl.
rewrite -> list_dissect with (i:=i) (l:= incl) at 3.
+ rewrite index_last.
  - rewrite size_behead -subn1 !size_cat -subnDA.
    assert(((#|R_i_greater_than mal init A w i t| + 1) = 
    1 + (#|R_i_greater_than mal init A w i t|))%N).
    {by rewrite addnC. }
    rewrite !size_sort H1 -!cardE.
    assert(((size incl + #|R_i_greater_than mal init A w i t|) -
    (1 + #|R_i_greater_than mal init A w i t|) = size incl - 1)%N).
    {by rewrite subnDr. }
    assert((#|R_i_less_than mal init A w i t| + (size incl + #|R_i_greater_than mal init A w i t|) -
    (1 + #|R_i_greater_than mal init A w i t|))%N = 
    (#|R_i_less_than mal init A w i t| + ((size incl + #|R_i_greater_than mal init A w i t|) -
    (1 + #|R_i_greater_than mal init A w i t|)))%N).
    {rewrite addnBA.
    + by [].
    + rewrite leq_add2r Heqincl. apply size_incl_not_0.
    }
    by rewrite H3 subnDr.
  - rewrite -list_dissect Heqincl.
    * apply incl_uniq.
    * apply incl_not_empty.
+ rewrite Heqincl. apply incl_not_empty.
Qed.

Lemma index_first_incl:
  forall (t:nat) (i:D) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  (index (nth i (incl_neigh_minus_extremes i (x mal init A w t)) 0)
  (inclusive_neighbor_list i (x mal init A w t)) = #|R_i_less_than mal init A w i t|)%N.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
rewrite (partition_incl i t mal init A w) !index_cat.
assert(nth i incl 0 \in enum (R_i_less_than mal init A w i t) = false).
{rewrite mem_enum. apply R_i_lt_and_incl_disjoint_0.
rewrite Heqincl. apply mem_nth, size_incl_not_0.
}
rewrite !mem_sort H size_sort.
assert(nth i incl 0 \in incl_neigh_minus_extremes i (x mal init A w t) = true).
{rewrite -Heqincl.
assert((nth i incl 0 \in incl)).
{rewrite Heqincl. apply mem_nth, size_incl_not_0. }
by [].
}
rewrite H0 -Heqincl -cardE index_uniq.
+ by rewrite addn0.
+ rewrite Heqincl. apply size_incl_not_0.
+ rewrite Heqincl. apply incl_uniq.
Qed.

Lemma card_R_i_gt_lt_F_exchange_last:
  forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  (#|R_i_greater_than mal init A w i t| < F)%N ->
  ((x mal init A w t (last (head i (incl_neigh_minus_extremes i (x mal init A w t)))
  (behead (incl_neigh_minus_extremes i (x mal init A w t))))) = (x mal init A w t i))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
assert((index (last (head i incl) (behead incl))
(inclusive_neighbor_list i (x mal init A w t)) =
(size (inclusive_neighbor_list i (x mal init A w t)) - #|R_i_greater_than mal init A w i t| - 1))%N).
{rewrite Heqincl. apply index_last_incl. }
assert(((#|R_i_greater_than mal init A w i t| + 1) < (F + 1))%N).
{unfold leq. unfold leq in H.
assert(((#|R_i_greater_than mal init A w i t|.+1 - F) = 0)%N).
{by apply /eqP. }
rewrite <- H1 at 3. by rewrite !addn1 subSS.
}
assert(#|incl| = size incl).
{apply /card_uniqP. rewrite Heqincl. apply incl_uniq. }
assert(i != (last (head i incl) (behead incl)) ->
(size (inclusive_neighbor_list i (x mal init A w t)) - (F + 1) <
size (inclusive_neighbor_list i (x mal init A w t)) - (#|R_i_greater_than mal init A w i t| + 1))%N).
{intros.
apply ltn_sub2l with (p:=(size (inclusive_neighbor_list i (x mal init A w t)))%N) in H1.
+ by [].
+ rewrite (partition_incl i t mal init A w) !size_cat !size_sort -!cardE addnA addnCAC.
  apply ltn_leq_trans with (n:=(#|R_i_greater_than mal init A w i t| +
  (size (incl_neigh_minus_extremes i (x mal init A w t))))%N).
  - rewrite -ltn_psubLR.
    * rewrite -addnBAC.
      ++ rewrite subnn addnC addn0 -Heqincl -H2. apply /card_gt1P.
         exists i. exists (last (head i incl) (behead incl)). split.
         -- rewrite Heqincl. apply i_in_incl.
         -- rewrite Heqincl. apply last_incl_in_incl.
         -- by [].
      ++ rewrite leq_eqVlt. apply /orP. by left.
    * apply size_incl_not_0.
  - by rewrite leq_addr.
}
apply Rle_antisym.
+ destruct (i == (last (head i incl) (behead incl)))%N eqn:E.
  - assert(i = (last (head i incl) (behead incl)))%N.
    {by apply /eqP. }
    rewrite -H4. by right.
  - assert((last (head i incl) (behead incl)) \notin
    R_i_greater_than mal init A w i t).
    {apply R_i_gt_and_incl_disjoint. rewrite Heqincl.
    apply last_incl_in_incl.
    }
    rewrite inE in H4.
    assert((last (head i incl) (behead incl) \in
    inclusive_neighbor_list i (x mal init A w t)) = true).
    {apply incl_subset_inclusive_neighbors
    with (t:=t) (mal:=mal) (init:= init) (A:=A) (w:=w).
    rewrite Heqincl. apply last_incl_in_incl.
    }
    rewrite H5 in H4.
    assert(true). {by []. }
    apply H3 in H6. rewrite !subnDA -H0 in H6.
    assert((size (inclusive_neighbor_list i (x mal init A w t)) - F - 1 <
    index (last (head i incl) (behead incl))
    (inclusive_neighbor_list i (x mal init A w t)))%N = true).
    {by []. }
    rewrite H7 !andb_true_r not_Rgt_Rle in H4. by destruct Rle_dec.
+ rewrite Heqincl. apply last_incl_is_max, i_in_incl.
Qed.

Lemma card_R_i_lt_lt_F_exchange_first:
forall (i j:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
(#|R_i_less_than mal init A w i t| < F)%N ->
((x mal init A w t (nth i (incl_neigh_minus_extremes i (x mal init A w t)) 0)) = (x mal init A w t i))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
assert((index (nth i incl 0) (inclusive_neighbor_list i (x mal init A w t)) =
#|R_i_less_than mal init A w i t|)%N).
{rewrite Heqincl. apply index_first_incl. }
assert(((#|R_i_less_than mal init A w i t| + 1) < (F + 1))%N).
{unfold leq. unfold leq in H.
assert(((#|R_i_less_than mal init A w i t|.+1 - F) = 0)%N).
{by apply /eqP. }
rewrite <- H1 at 3. by rewrite !addn1 subSS.
}
assert(#|incl| = size incl).
{apply /card_uniqP. rewrite Heqincl. apply incl_uniq. }
apply Rle_antisym.
+ destruct (i == (nth i incl 0))%N eqn:E.
  - assert(i = (nth i incl 0))%N.
    {by apply /eqP. }
    rewrite -H3. by right.
  - apply inclusive_neighbors_sorted_0 with (i:=i).
    * apply incl_subset_inclusive_neighbors with (t:=t) (mal:=mal) (init:=init) (A:=A) (w:=w).
      rewrite Heqincl. apply mem_nth, size_incl_not_0.
    * by apply i_in_inclusive_neighbors.
    * rewrite (partition_incl i t mal init A w) !index_cat.
      assert((nth i incl 0) \notin enum (R_i_less_than mal init A w i t)).
      {rewrite mem_enum. apply R_i_lt_and_incl_disjoint. rewrite Heqincl.
      apply mem_nth, size_incl_not_0.
      }
      assert(nth i incl 0 \in enum (R_i_less_than mal init A w i t) = false).
      {by destruct (nth i incl 0 \in enum (R_i_less_than mal init A w i t)) eqn:E0. }
      assert(nth i incl 0 \in incl_neigh_minus_extremes i (x mal init A w t) = true).
      {rewrite Heqincl. apply mem_nth, size_incl_not_0. }
      assert(i \notin enum (R_i_less_than mal init A w i t)).
      {rewrite mem_enum. apply R_i_lt_and_incl_disjoint, i_in_incl. }
      assert(i \in enum (R_i_less_than mal init A w i t) = false).
      {by destruct (i \in enum (R_i_less_than mal init A w i t)). }
      assert(i \in incl_neigh_minus_extremes i (x mal init A w t) = true).
      {apply i_in_incl. }
      rewrite !size_sort !mem_sort H4 H5 H7 H8 -!cardE Heqincl index_uniq.
      ++ rewrite addn0 -ltn_subLR.
         -- rewrite subnn.
            destruct (index i (incl_neigh_minus_extremes i (x mal init A w t)) == 0)%N eqn:E0.
            ** assert(index i (incl_neigh_minus_extremes i (x mal init A w t)) = 0)%N.
               {by apply /eqP. }
               rewrite -H9 Heqincl nth_index in E.
               +++ assert(i == i = true). {by apply /eqP. }
                   by rewrite H10 in E.
               +++ apply i_in_incl.
            ** by rewrite neq0_lt0n.
         -- by [].
      ++ apply size_incl_not_0.
      ++ apply incl_uniq.
+ assert((nth i incl 0) \notin R_i_less_than mal init A w i t).
  {apply R_i_lt_and_incl_disjoint. rewrite Heqincl.
  apply mem_nth, size_incl_not_0.
  }
  rewrite inE in H3.
  assert(((nth i incl 0) \in inclusive_neighbor_list i (x mal init A w t)) = true).
  {apply incl_subset_inclusive_neighbors with (t:=t) (mal:=mal) (init:=init) (A:=A) (w:=w).
  rewrite Heqincl. apply mem_nth, size_incl_not_0.
  }
  rewrite H4 in H3.
  assert((index (nth i incl 0) (inclusive_neighbor_list i (x mal init A w t)) < F)%N = true).
  {apply leq_ltn_trans with (n:=#|R_i_less_than mal init A w i t|).
  + rewrite (partition_incl i t mal init A w) !index_cat.
    assert(nth i incl 0 \in enum (R_i_less_than mal init A w i t) = false).
    {assert((nth i incl 0 \notin enum (R_i_less_than mal init A w i t))).
    {rewrite mem_enum. apply R_i_lt_and_incl_disjoint.
    rewrite Heqincl. apply mem_nth, size_incl_not_0. }
    by destruct (nth i incl 0 \in enum (R_i_less_than mal init A w i t)) eqn:E0.
    }
    rewrite !mem_sort !size_sort H5.
    assert(nth i incl 0 \in incl_neigh_minus_extremes i (x mal init A w t) = true).
    {rewrite Heqincl. apply mem_nth, size_incl_not_0. }
    rewrite H6 Heqincl index_uniq.
    - by rewrite -cardE addn0.
    - apply size_incl_not_0.
    - apply incl_uniq.
  + by [].
  }
  rewrite H5 !andb_true_r not_Rlt_Rge in H3.
  apply Rge_le. by destruct Rge_dec.
Qed.

Lemma in_normal_subset:
forall (i:D) (l : seq D) (A:D -> bool),
l != [::] ->  (forall (a:D), a \in l -> a \in (enum (Normal A))) ->
last (head i l) (behead l) \in Normal A.
Proof.
intros.
assert(last (head i l) (behead l) \in [set v | v \in enum (Normal A)] ->
last (head i l) (behead l) \in (Normal A)).
{by rewrite set_enum. }
apply H1. rewrite inE. apply H0.
assert(l = (head i l)::(behead l)). {by rewrite -list_dissect. }
rewrite -> H2 at 3. apply mem_last.
Qed.

Lemma in_normal_subset_0:
forall (i:D) (l : seq D) (A : D -> bool),
l != [::] -> (forall (a:D), a \in l -> a \in enum (Normal A)) ->
nth i l 0 \in (Normal A).
Proof.
intros. rewrite -mem_enum. apply H0. rewrite mem_nth.
+ by [].
+ destruct (size l == 0)%N eqn:E.
  - rewrite size_eq0 in E. by rewrite E in H.
  - by rewrite neq0_lt0n.
Qed.

Theorem Normal_adversary_disjoint:
forall (i:D) (A:D -> bool),
i \in Normal A <-> i \notin Adversary A.
Proof.
intros. split.
+ rewrite inE. intros. rewrite !inE andb_true_r in H.
  unfold negb. destruct (i \in Adversary A) eqn:E.
  - unfold Adversary in E. rewrite inE in E.
    assert(G: (A i = true)).
    {apply /eqP. by rewrite E. }
    rewrite G in H. discriminate.
  - by [].
+ rewrite inE. intros. unfold Normal. by rewrite !inE andb_true_r.
Qed.

Lemma R_i_gt_bounded:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
(#|R_i_greater_than mal init A w i t| <= F)%N.
Proof.
intros.
destruct (F < (size (inclusive_neighbor_list i (x mal init A w t))))%N eqn:E.
+ assert(F = size (filter (fun (j:D) => (index j (inclusive_neighbor_list i (x mal init A w t)) >
  ((size (inclusive_neighbor_list i (x mal init A w t))) - F - 1))%N)
  (inclusive_neighbor_list i (x mal init A w t)))).
  {rewrite subn1. rewrite filter_index_drop.
  + rewrite prednK.
    - rewrite size_drop subKn.
      * by [].
      * by apply ltnW in E.
    - by rewrite subn_gt0.
  + by [].
  + apply inclusive_neighbors_uniq.
  }
  rewrite H cardE. apply uniq_leq_size.
  - apply enum_uniq.
  - intros v H1. rewrite mem_filter. rewrite mem_enum inE in H1.
    apply /andP. split.
    * by apply andb_triple_inject_middle in H1.
    * by apply andb_triple_inject_right in H1.
+ assert((size (inclusive_neighbor_list i (x mal init A w t)) <= F)%N).
  {rewrite leqNgt. unfold negb. by rewrite E. }
  apply leq_trans with (n:=(size (inclusive_neighbor_list i (x mal init A w t)))%N).
  - rewrite cardE. apply uniq_leq_size.
    * apply enum_uniq.
    * intros v H0. rewrite mem_enum inE in H0.
      apply andb_triple_inject_right in H0.
    * by [].
  - by [].
Qed.

Lemma R_i_lt_bounded:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
(#|R_i_less_than mal init A w i t| <= F)%N.
Proof.
intros.
destruct (F < (size (inclusive_neighbor_list i (x mal init A w t))))%N eqn:E.
+ assert(F = size (filter (fun (j:D) => (index j (inclusive_neighbor_list i (x mal init A w t)) < F)%N)
  (inclusive_neighbor_list i (x mal init A w t)))).
  {rewrite filter_index_take.
  + by rewrite size_take E.
  + by [].
  + apply inclusive_neighbors_uniq.
  }
  rewrite H cardE. apply uniq_leq_size.
  - apply enum_uniq.
  - intros v H1. rewrite mem_filter. rewrite mem_enum inE in H1.
    apply /andP. split.
    * by apply andb_triple_inject_middle in H1.
    * by apply andb_triple_inject_right in H1.
+ assert((size (inclusive_neighbor_list i (x mal init A w t)) <= F)%N).
  {rewrite leqNgt. unfold negb. by rewrite E. }
  apply leq_trans with (n:=(size (inclusive_neighbor_list i (x mal init A w t)))%N).
  - rewrite cardE.
    apply uniq_leq_size.
    * apply enum_uniq.
    * intros v H0. rewrite mem_enum inE in H0.
      apply andb_triple_inject_right in H0.
    * by [].
  - by [].
Qed.

Lemma exists_j2:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
F_total_malicious mal init A w ->
wts_well_behaved A mal init w ->
i \in Normal A ->
(exists (j2:D), j2 \in (inclusive_neighbor_list i (x mal init A w t)) /\ j2 \in Normal A /\
forall (k:D), k \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
((x mal init A w t k) <= (x mal init A w t j2))%Re).
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
assert((#|R_i_greater_than mal init A w i t| <= F)%N \/
(#|R_i_greater_than mal init A w i t| > F)%N).
{apply /orP. destruct (#|R_i_greater_than mal init A w i t| <= F)%N eqn:E.
+ by [].
+ by rewrite /= leqNgt ltnS E.
}
destruct H2.
+ assert ((#|R_i_greater_than mal init A w i t| == F)%N \/
  (#|R_i_greater_than mal init A w i t| < F)%N).
  {apply /orP. by rewrite -leq_eqVlt. }
  destruct H3.
  - assert(R_i_greater_than mal init A w i t == Adversary A \/
    R_i_greater_than mal init A w i t != Adversary A).
    {apply /orP.
    by destruct (R_i_greater_than mal init A w i t == Adversary A).
    }
    destruct H4. (** the j2 here is the last elt of J\R_i[t] **)
    * exists (last (head i incl) (behead incl)).
      split.
      ++ apply incl_subset_inclusive_neighbors with (mal:=mal) (init:=init) (A:=A) (w:=w) (t:=t).
         rewrite Heqincl. apply last_incl_in_incl.
      ++ split.
         -- assert(R_i_greater_than mal init A w i t = Adversary A).
            {by apply /eqP. }
            apply in_normal_subset.
            ** rewrite Heqincl. apply incl_not_empty.
            ** intros.
               rewrite Heqincl incl_set_version mem_filter in H6.
               assert(a \notin R_i_greater_than mal init A w i t).
               {apply andb_triple_inject_middle in H6.
               by apply R_i_gt_mnn_subset_R_i_gt in H6.
               }
               rewrite H5 in H7. apply Normal_adversary_disjoint in H7.
               by rewrite mem_enum.
         -- intros. rewrite Heqincl. apply last_incl_is_max.
            rewrite -Heqincl. exact H5.
    * assert((exists (j:D), j \in Normal A /\
      j \in R_i_greater_than mal init A w i t)).
      {by apply exists_normal_node_in_R_i_gt. }
      elim H5. intros v H6. exists v. destruct H6. split.
      ++ rewrite inE in H7. by apply andb_triple_inject_right in H7.
      ++ split.
         -- exact H6.
         -- intros.
            apply Rle_trans with (r2:=x mal init A w t
            (last (head i incl) (behead incl))).
            ** rewrite Heqincl. rewrite Heqincl in H8.
               by apply last_incl_is_max.
            ** rewrite Heqincl. rewrite Heqincl in H8.
               by apply in_R_i_gt_bounds_incl.
  - exists i. split.
    * by apply i_in_inclusive_neighbors.
    * split.
      ++ by [].
      ++ rewrite -card_R_i_gt_lt_F_exchange_last.
         -- rewrite Heqincl. intros. by apply last_incl_is_max.
         -- by [].
         -- by [].
+ assert((#|R_i_greater_than mal init A w i t| <= F)%N). {apply R_i_gt_bounded. }
  assert((F != #|R_i_greater_than mal init A w i t|)%N).
  {rewrite neq_ltn. apply /orP. by left. }
  assert((F < F)%N).
  {apply ltn_trans with (n:=#|R_i_greater_than mal init A w i t|).
  + by [].
  + rewrite ltn_neqAle. apply /andP. split.
    - rewrite neq_ltn. apply /orP. by right.
    - by [].
  }
  by rewrite ltnn in H5.
Qed.

Lemma exists_j1:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
F_total_malicious mal init A w ->
wts_well_behaved A mal init w ->
i \in Normal A ->
(exists (j1:D), j1 \in (inclusive_neighbor_list i (x mal init A w t)) /\ j1 \in Normal A /\
forall (k:D), k \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
((x mal init A w t j1) <= (x mal init A w t k))%Re).
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A w t)) as incl.
assert((#|R_i_less_than mal init A w i t| <= F)%N).
{apply R_i_lt_bounded. }
rewrite leq_eqVlt in H2.
assert(R_i_less_than mal init A w i t == Adversary A \/
R_i_less_than mal init A w i t != Adversary A).
{apply /orP. by destruct (R_i_less_than mal init A w i t == Adversary A). }
assert((#|R_i_less_than mal init A w i t| == F)
\/ (#|R_i_less_than mal init A w i t| < F)%N). {by apply /orP. }
destruct H4.
+ destruct H3.
  - assert(R_i_less_than mal init A w i t = Adversary A). {by apply /eqP. }
    exists (nth i incl 0%N). split.
    * assert(nth i incl 0 \in incl).
      {rewrite mem_nth. 
      + by [].
      + rewrite Heqincl. apply size_incl_not_0.
      }
      rewrite Heqincl in H6. apply incl_subset_inclusive_neighbors in H6.
      by rewrite Heqincl.
    * split.
      ++ apply in_normal_subset_0.
         -- rewrite Heqincl. apply incl_not_empty.
         -- intros.
            rewrite Heqincl incl_set_version mem_filter in H6.
            assert(a \notin R_i_less_than mal init A w i t).
            {apply andb_triple_inject_left in H6.
            by apply R_i_lt_mnn_subset_R_i_lt.
            }
            rewrite H5 in H7. apply Normal_adversary_disjoint in H7.
            by rewrite mem_enum.
      ++ rewrite Heqincl. intros.
         by apply first_incl_is_min with (i:=i) (t:=t).
  - assert((exists (j:D), j \in Normal A /\
    j \in R_i_less_than mal init A w i t)).
    {by apply exists_normal_node_in_R_i_lt. }
    elim H5. intros v H6. exists v. destruct H6. split.
    * assert(v \in R_i_less_than mal init A w i t). {by []. }
      rewrite inE in H8.
      by apply andb_triple_inject_right in H8.
    * split.
      ++ by [].
      ++ intros.
         apply Rle_trans with (r2:=x mal init A w t (nth i incl 0)).
         -- rewrite Heqincl. by apply in_R_i_lt_bounds_incl.
         -- destruct (k == (nth i incl 0)) eqn:E.
            ** assert(k = nth i incl 0). {by apply /eqP. }
               rewrite -H9. by right.
            ** rewrite Heqincl. apply incl_sorted with (mal:=mal) (init:=init) (A:=A) (w:=w) (i:=i) (t:=t).
               +++ apply mem_nth, size_incl_not_0.
               +++ by rewrite -Heqincl.
               +++ rewrite index_uniq.
                   --- destruct (0 == index k (incl_neigh_minus_extremes i (x mal init A w t)))%N eqn:E0.
                       *** assert(0 = index k (incl_neigh_minus_extremes i (x mal init A w t)))%N.
                           {by apply /eqP. }
                           assert(k == k = true). {by apply /eqP. }
                           rewrite H9 -Heqincl nth_index in E.
                           ++++ by rewrite E in H10.
                           ++++ by [].
                       *** rewrite eq_sym in E0.
                           by apply neq0_lt0n.
                   --- apply size_incl_not_0.
                   --- apply incl_uniq.
    * exists i. split.
      ++ by apply i_in_inclusive_neighbors.
      ++ split.
         -- by [].
         -- rewrite -card_R_i_lt_lt_F_exchange_first.
            ** rewrite Heqincl. intros. by apply first_incl_is_min.
            ** by [].
            ** by [].
Qed.

Theorem w_coeff_sum_to_1_implies_sum_eq_orig:
  forall (i:D) (t:nat) (r:R) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  sum_f_R0 (fun n : nat =>
  w t (i, nth i (incl_neigh_minus_extremes i (x mal init A w t)) n))
  (size (incl_neigh_minus_extremes i (x mal init A w t)) - 1) = 1 -> (sum_f_R0 (fun n:nat =>
  ((w t (i,(nth i (incl_neigh_minus_extremes i (x mal init A w t)) n))) * r)%Re)
  ((size (incl_neigh_minus_extremes i (x mal init A w t)))-1) = r).
Proof.
intros. by rewrite -scal_sum H Rmult_1_r.
Qed.

Lemma lem_1:
forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
F_total_malicious mal init A w ->
wts_well_behaved A mal init w ->
i \in Normal A ->
((x mal init A w (t+1) i <= M mal init A w t)%Re /\
(m mal init A w t <= x mal init A w (t+1) i)%Re).
Proof.
intros.
assert(A i = false).
{apply Normal_adversary_disjoint in H1.
rewrite inE in H1. unfold negb in H1. by destruct (A i).
}
split.
+ induction t as [|t' IHt'].
  - assert(aux1: i \in Normal A). {by []. }
    assert(aux2: wts_well_behaved A mal init w). {by []. }
    rewrite /wts_well_behaved in H0.
    destruct H0 as [a H0].
    destruct H0. destruct H3.
    specialize (H4 0%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig
    with (r:=(M mal init A w 0)) (mal:=mal) (init:=init) (A:=A) (w:=w) (i:=i) (t:=0%N).
    rewrite /= H2.
    apply sum_Rle.
    intros n H7.
    rewrite Rmult_comm.
    apply Rmult_le_compat_l.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x mal init A w 0)) = 
         (size (incl_neigh_minus_extremes i (x mal init A w 0)) - 1).+1).
         {rewrite subn1 prednK.
         + by [].
         + apply size_incl_not_0.
         } rewrite H8 ltnS. by apply /leP.
    * unfold M.
      assert((exists (j2:D), j2 \in (inclusive_neighbor_list i (x mal init A w 0)) /\
      j2 \in Normal A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x mal init A w 0)) ->
      ((x mal init A w 0 k) <= (x mal init A w 0 j2))%Re)).
      {by apply exists_j2. }
      elim H8.
      intros v H9.
      destruct H9. destruct H10.
      apply Rle_trans with (r2:= (x mal init A w 0 v)).
      ++ apply H11, mem_nth.
         assert((n <= size (incl_neigh_minus_extremes i (x mal init A w 0)) - 1)%N).
         {by apply /leP. }
         rewrite subn1 -ltnS prednK in H12.
         -- by [].
         -- rewrite -has_predT. apply /hasP. exists i.
            ** apply i_in_incl.
            ** by [].
      ++ remember [seq x mal init A w 0 i | i <- enum (Normal A)] as x_incl.
         rewrite <- nth_index with (x0:=0) (x:= x mal init A w 0 v)
         (s:=x_incl). 
         -- apply /RlebP.
            apply bigmaxr_ler with (x0:=0) (s:=x_incl)
            (i0:=(index (x mal init A w 0 v) x_incl)).
            rewrite Heqx_incl index_mem.
            apply map_f. by rewrite mem_enum.
         -- rewrite Heqx_incl. apply map_f. by rewrite mem_enum.
    * by [].
  - rewrite /= H2.
    assert(aux1: i \in Normal A). {by []. }
    assert(aux2: wts_well_behaved A mal init w). {by []. }
    rewrite /wts_well_behaved in H0.
    destruct H0 as [a H0]. destruct H0. destruct H3.
    specialize (H4 (t'.+1)%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig with
    (init:=init) (mal:=mal) (A:=A) (w:=w) (r:=(M mal init A w t'.+1)) (i:=i) (t:=t'.+1%N).
    rewrite -addnE addn1. apply sum_Rle. intros n H7.
    rewrite Rmult_comm. apply Rmult_le_compat_l.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x mal init A w (t'.+1))) = 
         (size (incl_neigh_minus_extremes i (x mal init A w (t'.+1))) - 1).+1).
         {rewrite subn1 prednK.
         + by [].
         + apply size_incl_not_0.
         }
         rewrite H8 ltnS.
         by apply /leP.
    * assert((exists (j2:D), j2 \in (inclusive_neighbor_list i (x mal init A w t'.+1)) /\
      j2 \in Normal A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x mal init A w (t'.+1))) ->
      ((x mal init A w (t'.+1) k) <= (x mal init A w (t'.+1) j2))%Re)).
      {by apply exists_j2. }
      elim H8. intros v H9.
      apply Rle_trans with (r2:= (x mal init A w (t'.+1) v)).
      ++ destruct H9. destruct H10. apply H11. rewrite mem_nth.
         -- by [].
         -- assert((n <= size (incl_neigh_minus_extremes i (x mal init A w (t'.+1))) - 1)%N).
            {by apply /leP. }
            rewrite subn1 -ltnS prednK in H12.
            ** by []. 
            ** rewrite -has_predT. apply /hasP. exists i.
               +++ apply i_in_incl.
               +++ by [].
      ++ unfold M. destruct H9. destruct H10.
         remember [seq x mal init A w (t'.+1) i | i <- enum (Normal A)] as x_incl.
         rewrite <- nth_index with (x0:=0) (x:= x mal init A w (t'.+1) v)
         (s:=x_incl). 
         -- apply /RlebP. unfold M.
            apply bigmaxr_ler with (x0:=0) (s:=x_incl)
            (i0:=(index (x mal init A w (t'.+1) v) x_incl)).
            rewrite Heqx_incl index_mem. apply map_f.
            by rewrite mem_enum.
         -- rewrite Heqx_incl. apply map_f. by rewrite mem_enum.
      ++ by [].
+ induction t as [|t' IHt'].
  - assert(aux1: i \in Normal A). {by []. }
    assert(aux2: wts_well_behaved A mal init w). {by []. }
    rewrite /wts_well_behaved in H0.
    destruct H0 as [a H0]. destruct H0. destruct H3.
    specialize (H4 0%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig
    with (r:=(m mal init A w 0)) (mal:=mal) (init:=init) (A:=A) (w:=w) (i:=i) (t:=0%N).
    rewrite /= H2. apply sum_Rle. intros n H7. rewrite Rmult_comm.
    apply Rmult_le_compat_r.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x mal init A w 0)) = 
         (size (incl_neigh_minus_extremes i (x mal init A w 0)) - 1).+1).
         {rewrite subn1 prednK.
         + by [].
         + apply size_incl_not_0.
         }
         rewrite H8 ltnS.
         by apply /leP.
    * unfold m.
      assert(exists (j1:D), j1 \in
      (inclusive_neighbor_list i (x mal init A w 0)) /\ j1 \in Normal A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x mal init A w 0)) ->
      ((x mal init A w 0 j1) <= (x mal init A w 0 k))%Re).
      {by apply exists_j1. }
      elim H8.
      intros v H9.
      destruct H9. destruct H10.
      rewrite -mem_enum in H10.
      apply Rle_trans with (r2:= (x mal init A w 0 v)).
      ++ remember [seq (- x mal init A w 0 i) | i <- enum (Normal A)] as x_incl.
         remember [seq (x mal init A w 0 i) | i <- enum (Normal A)] as pos_x_incl.
         rewrite <- nth_index with (x0:=0) (x:= (x mal init A w 0 v))
         (s:=pos_x_incl).
         -- assert(pos_x_incl`_(index ((x mal init A w 0 v)) pos_x_incl) =
            - - pos_x_incl`_(index ((x mal init A w 0 v)) pos_x_incl))%Re.
            {by rewrite Ropp_involutive. }
            rewrite H12.
            apply Ropp_le_contravar.
            assert(- pos_x_incl`_(index (x mal init A w 0 v) pos_x_incl) =
            x_incl`_(index (- (x mal init A w 0 v)) x_incl))%Re.
            {rewrite nth_index.
            + rewrite nth_index.
              - by [].
              - rewrite Heqx_incl.
                apply /mapP.
                by exists v.
            + rewrite Heqpos_x_incl.
              apply /mapP.
              by exists v.
            }
            rewrite H13. apply /RlebP.
            apply bigmaxr_ler with (x0:=0) (s:= x_incl)
            (i0:=(index (- (x mal init A w 0 v)) x_incl)).
            rewrite Heqx_incl index_mem. apply /mapP. by exists v.
         -- rewrite Heqpos_x_incl. apply /mapP. by exists v.
      ++ apply H11, mem_nth.
         assert((n <= size (incl_neigh_minus_extremes i (x mal init A w 0)) - 1)%N).
         {by apply /leP. }
         rewrite subn1 -ltnS prednK in H12.
         -- by [].
         -- rewrite -has_predT. apply /hasP. exists i.
            ** apply i_in_incl.
            ** by [].
    * by [].
  - rewrite /= H2.
    assert(aux1: i \in Normal A). {by []. }
    assert(aux2: wts_well_behaved A mal init w). {by []. }
    rewrite /wts_well_behaved in H0.
    destruct H0 as [a H0]. destruct H0. destruct H3.
    specialize (H4 (t'.+1)%N i).
    destruct H4. destruct H5.
    rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig with
    (mal:=mal) (init:=init) (A:=A) (w:=w) (r:=(m mal init A w t'.+1)) (i:=i) (t:=t'.+1%N).
    rewrite -addnE addn1. apply sum_Rle. intros n H7.
    rewrite Rmult_comm. apply Rmult_le_compat_r.
    * apply Rle_trans with a.
      ++ nra.
      ++ apply H5. apply mem_nth.
         assert(size (incl_neigh_minus_extremes i (x mal init A w (t'.+1))) = 
         (size (incl_neigh_minus_extremes i (x mal init A w (t'.+1))) - 1).+1).
         {rewrite subn1 prednK.
         + by [].
         + apply size_incl_not_0.
         }
         rewrite H8 ltnS. by apply /leP.
    * assert(exists (j1:D), j1 \in
      (inclusive_neighbor_list i (x mal init A w t'.+1)) /\ j1 \in Normal A /\
      forall (k:D), k \in (incl_neigh_minus_extremes i (x mal init A w t'.+1)) ->
      ((x mal init A w t'.+1 j1) <= (x mal init A w t'.+1 k))%Re).
      {by apply exists_j1. }
      elim H8. intros v H9. destruct H9. destruct H10.
      rewrite -mem_enum in H10.
      apply Rle_trans with (r2:= (x mal init A w (t'.+1) v)).
      ++ remember [seq (- x mal init A w t'.+1 i) | i <- enum (Normal A)] as x_incl.
         remember [seq (x mal init A w t'.+1 i) | i <- enum (Normal A)] as pos_x_incl.
         rewrite <- nth_index with (x0:=0) (x:= (x mal init A w t'.+1 v))
         (s:=pos_x_incl).
         -- assert(pos_x_incl`_(index ((x mal init A w t'.+1 v)) pos_x_incl) =
            - - pos_x_incl`_(index ((x mal init A w t'.+1 v)) pos_x_incl))%Re.
            {by rewrite Ropp_involutive. }
            rewrite H12. apply Ropp_le_contravar.
            assert(- pos_x_incl`_(index (x mal init A w t'.+1 v) pos_x_incl) =
            x_incl`_(index (- (x mal init A w t'.+1 v)) x_incl))%Re.
            {rewrite nth_index.
            + rewrite nth_index.
              - by [].
              - rewrite Heqx_incl.
                apply /mapP.
                by exists v.
            + rewrite Heqpos_x_incl.
              apply /mapP.
              by exists v.
            }
            rewrite H13 -Heqx_incl. apply /RlebP.
            apply bigmaxr_ler with (x0:=0) (s:= x_incl)
            (i0:=(index (- (x mal init A w t'.+1 v)) x_incl)).
            rewrite Heqx_incl index_mem. apply /mapP. by exists v.
         -- rewrite Heqpos_x_incl. apply /mapP. by exists v.
      ++ apply H11, mem_nth.
         assert((n <= size (incl_neigh_minus_extremes i (x mal init A w t'.+1)) - 1)%N).
         {by apply /leP. }
         rewrite subn1 -ltnS prednK in H12.
         -- by [].
         -- rewrite -has_predT. apply /hasP. exists i.
            ** apply i_in_incl.
            ** by [].
    * by [].
Qed.
