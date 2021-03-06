Require Import Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra finset.
From GraphTheory Require Import digraph.
From Coquelicot Require Import Lim_seq Rbar.
From mathcomp.analysis Require Import Rstruct.
From Coq Require Import Logic.Classical_Pred_Type Logic.FunctionalExtensionality Bool.Bool.
Require Import definitions.
Require Import Coq.Logic.ClassicalFacts Coq.Init.Datatypes.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import lemma_1.

Notation D:= definitions.D.
Notation F:= definitions.F.


Lemma excluded_middle:
  forall A :Prop, A \/ ~A.
Proof.
intros.
assert ( A = True \/ A = False).
{ by apply proposition_degeneracy. } destruct H.
+ rewrite H. by left.
+ rewrite H. by right.
Qed.

Lemma de_morgan_and:
  forall A B:Prop, ~(A /\ B) -> ~A \/ ~B.
Proof.
intros.
assert (A = True \/ A = False). { by apply proposition_degeneracy. }
destruct H0.
+ rewrite H0. rewrite H0 //= in H.
  right. 
  assert (B = True \/ B = False). { by apply proposition_degeneracy. }
  destruct H1. 
  - rewrite H1 in H. by contradict H. 
  - by rewrite H1.
+ rewrite H0. by left.
Qed.



Lemma de_morgan_or:
  forall A B:Prop, ~(A \/ B) -> ~A /\ ~B.
Proof.
intros.
assert (A = True \/ A = False). { by apply proposition_degeneracy. }
destruct H0.
+ rewrite H0 in H. 
  assert (B = True \/ B = False). { by apply proposition_degeneracy. }
  destruct H1. 
  - rewrite H1 in H. contradict H. by left.
  - rewrite H1 in H. contradict H. by left.
+ rewrite H0. split.
  - by [].
  - rewrite H0 in H.
    assert (B = True \/ B = False). { by apply proposition_degeneracy. }
    destruct H1.
    * rewrite H1 in H. contradict H. by right.
    * by rewrite H1.
Qed.


Lemma nandb_triple:
  forall (a b c:bool), ~~(a || b || c) <-> ~~a && ~~b && ~~c.
Proof.
intros. split.
+ intro. destruct a.
  - by [].
  - destruct b.
    * by [].
    * by destruct c.
+ intro. destruct a.
  - by [].
  - destruct b.
    * by [].
    * by destruct c.
Qed.

Lemma andb_triple_prop:
  forall (a b c:bool), a && b && c <-> a /\ b /\ c.
Proof.
intros. split.
+ intro.
  assert(a). {by apply andb_triple_inject_left in H. }
  assert(b). {by apply andb_triple_inject_middle in H. }
  assert(c). {by apply andb_triple_inject_right in H. }
  rewrite H0 H1 H2.
  by split.
+ intro. destruct H. destruct H0.
  by rewrite H H0 H1 /=.
Qed.

Lemma norb:
  forall (a b:bool), ~~(a || b) = ~~ a && ~~ b.
Proof.
intros. destruct a.
+ by [].
+ by destruct b.
Qed.

Lemma not_gt_lt:
  forall (n m:nat), ~~(n <= m)%N <-> (m < n)%nat.
Proof.
intros. by rewrite ltnNge.
Qed.

Lemma bigmax_le (x0:R) lr (x:R):
 (0 < size lr)%N ->
 (forall i:nat, (i < size lr)%N -> ((nth x0 lr i) <= x)%Re) ->
 ((bigmaxr x0 lr) <= x)%Re.
Proof.
intros.
move /(nthP x0): (bigmaxr_mem x0 H).
move => [i i_size <-].
by apply H0.
Qed.

Lemma bigmax_lt (x0:R) lr (x:R):
 (0 < size lr)%N ->
 (forall i:nat, (i < size lr)%N -> ((nth x0 lr i) < x)%Re) ->
 ((bigmaxr x0 lr) < x)%Re.
Proof.
intros.
move /(nthP x0): (bigmaxr_mem x0 H).
move => [i i_size <-].
by apply H0.
Qed.

Lemma implies_as_or:
  forall (P Q: Prop), ~(P /\ Q) <-> (~P \/ ~Q).
Proof.
intros. split. 
+ apply de_morgan_and.
+ intros. unfold not. intros. destruct H0.
  destruct H.
  - unfold not in H. by apply H.
  - unfold not in H. by apply H.
Qed.

Lemma implies_as_and:
  forall (P Q: Prop), ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
intros. split. 
+ apply de_morgan_or.
+ intros. unfold not. intros. destruct H0.
  destruct H.
  - unfold not in H. by apply H.
  - unfold not in H. by apply H.
Qed.

Lemma not_implies_as_and:
  forall (P Q: Prop), ~(P -> Q) <-> (P /\ ~Q).
Proof.
intros.
assert ((P -> Q) <-> ~P \/ Q).
{ split.
  + intros. 
    assert (P \/ ~P). { apply excluded_middle. } destruct H0.
    - specialize (H H0). by right.
    - by left.
  + intros.  destruct H.
    - contradiction.
    - by [].
} rewrite H. rewrite implies_as_and.
+ intros. by rewrite -P_not_not_P.
Qed.


Lemma add_max_bound: forall (B C F:nat),
  (F+1 <= B+C)%N -> (C <= F)%N -> (1 <= B)%N.
Proof.
intros. 
assert ( 1 = ((F+1) - F))%N.
{rewrite addn1. by rewrite subSnn. }
rewrite H1.
assert (B = ((B+C) - (0 + C))%N).
{ assert (B = (B-0)%N). { by rewrite subn0. }
  rewrite [in LHS]H2. by rewrite subnDr.
} rewrite H2. rewrite add0n.
by apply leq_sub.
Qed.

Lemma normal_or_adversary: forall (i:D) (A: D -> bool), 
  ( i \in (Normal A)) \/ (i \in (Adversary A)).
Proof.
intros. apply /orP. rewrite -in_setU.
assert (Adversary A = ~: Normal A).
{ apply eq_finset. unfold eqfun. intros. rewrite !inE.
  by destruct (A x == true).
} rewrite H. by rewrite setUCr.
Qed.

Lemma a_and_b_false_implies: forall (a b: bool),
  (a -> (~~b)) ->
  (a && b = false).
Proof.
intros. destruct a.
+ assert (true). { by []. } specialize (H H0).
  destruct b.
  - by simpl in H.
  - by [].
+ by [].
Qed.

Lemma Normal_not_adversary (A: D -> bool):
  Normal A = ~:Adversary A.
Proof.
apply eq_finset. unfold eqfun. intros. 
destruct ((x \notin Adversary A)).
+ by rewrite in_setT.
+ by [].
Qed.


Lemma cardD_sum (A: D -> bool): 
  #|D| =( #|Normal A| + #|Adversary A|)%N.
Proof.
rewrite -cardsUI.
assert (#|Normal A :&: Adversary A| = 0%N).
{ apply /eqP. rewrite cards_eq0. apply /eqP.
  apply eq_finset. unfold eqfun. move =>k.
  apply a_and_b_false_implies.
  intros. rewrite -in_setC. by rewrite -Normal_not_adversary.
} rewrite H addn0. rewrite Normal_not_adversary.
rewrite setUC setUCr. by rewrite cardsT.
Qed.


Lemma size_normal_gt_0 (A: D -> bool): 
  F_totally_bounded A ->
  (0 < F + 1 <= #|D|)%N -> 
  (0 < size (enum (Normal A)))%N.
Proof.
intros. 
assert ((0 < F+1)%N /\ (F+1 <= #|D|)%N).
{ by apply /andP. } destruct H1. rewrite -cardE.
rewrite (cardD_sum A) in H2. 
apply (@add_max_bound #|Normal A| #|Adversary A| F) in H2.
+ by [].
+ rewrite /F_totally_bounded /F_total in H. by destruct H.
Qed.


Variable key:D.

Lemma in_enum_Normal: forall (i:D) (l:{set D}),
  i \in enum l -> i \in l.
Proof.
intros.  
assert ([set x | x \in enum l] = l).
{ apply set_enum. } rewrite -H0.
by rewrite inE.
Qed.


Lemma nth_normal: forall (i:nat) (A: D -> bool), 
  (i < size (enum (Normal A)))%N ->  
  nth key (enum (Normal A)) i \in (Normal A).
Proof.
intros.
assert ( nth key (enum (Normal A)) i \in enum (Normal A) ->
          nth key (enum (Normal A)) i \in (Normal A)).
{ apply (@in_enum_Normal (nth key (enum (Normal A)) i) (Normal A)). }
by apply H0, mem_nth.
Qed.

Lemma interval_bound:
  forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
  F_total_malicious mal init A w ->
  wts_well_behaved A mal init w ->
  (0 < F + 1 <= #|D|)%N ->
  forall t : nat,
  (m mal init A w 0 <= m mal init A w t)%Re /\
  (M mal init A w t <= M mal init A w 0)%Re.
Proof.
intros. induction t.
  - nra.
  - destruct IHt as [mIHt MIHt].
    split.
    * apply Rle_trans with (m mal init A w t)%Re.
      ++ apply mIHt.
      ++ assert (m mal init A w t.+1 = 
                  -(bigmaxr 0 ((map (fun i:D => -(x mal init A w t.+1 i))) (enum (Normal A))))).
         { by rewrite /m. } rewrite H2. clear H2.
         assert ( m mal init A w t = (-(-(m mal init A w t)))%Re). { by rewrite Ropp_involutive. }
         rewrite H2. apply Ropp_ge_le_contravar.
         apply Rle_ge. apply bigmax_le.
         - rewrite size_map. destruct H. by apply size_normal_gt_0.
         - intros. rewrite size_map in H3.
           assert ( nth 0%Re ((map (fun i:D => -(x mal init A w t.+1 i))) (enum (Normal A))) i= 
                      (fun i:D => - (x mal init A w t.+1 i)) (nth key (enum (Normal A)) i)).
           { by apply (@nth_map D key R 0%Re (fun i:D => -(x mal init A w t.+1 i)) i (enum (Normal A))). }
           rewrite H4. apply Ropp_ge_le_contravar. apply Rle_ge.
           assert (forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
                    F_total_malicious mal init A w ->
                    wts_well_behaved A mal init w ->
                    i \in Normal A ->
                    ((x mal init A w (t+1) i <= M mal init A w t)%Re /\
                    (m mal init A w t <= x mal init A w (t+1) i)%Re)).
           { apply lem_1. }
           specialize (H5 (nth key (enum (Normal A)) i)).
           specialize (H5 t mal init A w H H0).
           assert (nth key (enum (Normal A)) i \in (Normal A)). 
           { apply nth_normal, H3. }
           specialize (H5 H6). rewrite -addn1. destruct H5.
           apply H7.
    * apply Rle_trans with (M mal init A w t)%Re.
      ++ assert (M mal init A w t.+1 = bigmaxr 0 (map (x mal init A w t.+1) (enum (Normal A)))).
         { by rewrite /M. } rewrite H2. clear H2.
         apply bigmax_le.
         - rewrite size_map. destruct H. by apply size_normal_gt_0.
         - intros. rewrite size_map in H2.
           assert ( [seq x mal init A w t.+1 i | i <- enum (Normal A)]`_i = 
                      (fun i:D => (x mal init A w t.+1 i)) (nth key (enum (Normal A)) i)).
           { by apply nth_map. } rewrite H3.
           assert (forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
                    F_total_malicious mal init A w ->
                    wts_well_behaved A mal init w ->
                    i \in Normal A ->
                    ((x mal init A w (t+1) i <= M mal init A w t)%Re /\
                    (m mal init A w t <= x mal init A w (t+1) i)%Re)).
           { apply lem_1. }
           specialize (H4 (nth key (enum (Normal A)) i)).
           specialize (H4 t mal init A w H H0).
           assert (nth key (enum (Normal A)) i \in (Normal A)). 
           { apply nth_normal, H2. }
           specialize (H4 H5). rewrite -addn1. destruct H4.
           apply H4.
      ++ apply MIHt.
Qed.


Lemma temp_name_2:
  forall (A B C: bool),
  ~(A || B || C) <-> (~~A /\ ~~B /\ ~~C).
Proof.
intros. destruct A.
+ simpl. split.
  - intros. 
    assert (~~ true). { by apply /negP. } by simpl in H0.
  - intros. 
    assert (false  && ~~B && ~~C).
    { apply /andP. destruct H. destruct H0. split.
      + by apply /andP.
      + by [].
    } by simpl in H0. 
+ simpl. split.
  - intros. simpl. split.
    * by [].
    * assert (~~ (B || C)). { by apply /negP. }
      assert ( ~~ B && ~~C).
      { destruct B.
        + by simpl in H0.
        + simpl. by destruct C.
      } by apply /andP.
  - intros. destruct H. apply /negP. by apply /norP.
Qed.

Lemma temp_name_1:
  (0 < F + 1 <= #|D|)%N ->
  ~ r_s_robustness (F + 1) (F + 1) ->
  exists (S1 S2: {set D}), 
  (S1 \proper Vertex) /\ (0 < #|S1|)%N ->
  (S2 \proper Vertex) /\ (0 < #|S2|)%N -> [disjoint S1 & S2] ->
  (#|Xi_S_r S1 (F + 1)| != #|S1|) && 
  (#|Xi_S_r S2 (F + 1)| != #|S2|) &&
  (#|Xi_S_r S1 (F + 1)| + #|Xi_S_r S2 (F + 1)| < (F + 1))%N.
Proof.
  intros.
  unfold r_s_robustness in H0.
  apply implies_as_or in H0.
  destruct H0.
  + unfold nonempty_nontrivial_graph in H0.
    assert (~~(1 < #|D|)%N). { by apply /negP. }
    rewrite -leqNgt in H1.
    rewrite leq_eqVlt in H1.
    assert ( (#|D| == 1%N) \/ (#|D| < 1)%N).
    { by apply /orP. }
    destruct H2.
    - assert (#|D| = 1%N). { by apply /eqP. } rewrite H3 in H.
      exists set0. exists [set x | x \in Vertex].
      intros. rewrite cards0 in H4. by destruct H4.
    - apply ltnSE in H2. rewrite leqn0 in H2.
      assert (#|D| = 0%N). { by apply /eqP. } rewrite H3 in H.
      assert ((0 < F+1)%N /\ (F+1 <= 0)%N).
      { by apply /andP. } destruct H4.
      rewrite leqNgt in H5.
      assert ((0 < F + 1)%N). { by rewrite addn1. }
      assert ( ~ (0 < F + 1)%N). { by apply /negP. } contradiction.
  + apply -> not_implies_as_and in H0.
    destruct H0.
    apply not_all_ex_not in H1.
    elim H1.
    intros S1 H2.
    apply not_all_ex_not in H2.
    elim H2.
    intros S2 H3.
    exists S1. exists S2.
    apply -> not_implies_as_and in H3.
    destruct H3.
    apply -> not_implies_as_and in H4.
    destruct H4.
    apply -> not_implies_as_and in H5.
    destruct H5. intros. apply temp_name_2 in H6.
    destruct H6. destruct H10. apply /andP.
    split.
    + by apply /andP.
    + by rewrite -ltnNge in H11. 
Qed.



Lemma norb_triple:
  forall (A B C: bool),
  ~~(A && B && C) <-> (~~A || ~~B || ~~C).
Proof.
intros. split.
+ intros. destruct A.
  - simpl. simpl in H. by destruct B.
  - by simpl.
+ intros. destruct A.
  - simpl. simpl in H. apply /nandP.
    by apply /orP.
  - by simpl.
Qed.

Lemma orb_triple:
  forall (A B C: bool),
  (A || B || C) <-> (A \/ B \/ C).
Proof.
intros. split.
+ intros. destruct A.
  - by left.
  - simpl in H. right. by apply /orP.
+ intros. destruct A.
  - by simpl.
  - simpl in H. simpl. destruct B.
    * by simpl.
    * simpl. destruct C.
      ++ by [].
      ++ destruct H. 
         ++ by [].
         ++ by destruct H.
Qed.

Lemma nand_temp:
  forall (P Q:Prop),
  ~ (P /\ Q) <-> ~P \/ ~Q.
Proof.
intros. apply implies_as_or.
Qed.

Lemma zero_sum_is_zero:
  forall (An:nat -> R), (forall (n0:nat), (An n0 = 0)%Re) ->
  forall (n:nat), (sum_f_R0 An n = 0)%Re.
Proof.
intros. induction n.
+ simpl. by apply H.
+ simpl. rewrite IHn. rewrite Rplus_0_l. by apply H.
Qed.

Lemma sum_Rle_0:
  forall (An:nat -> R) (N:nat),
  (forall n:nat, (n <= N)%nat -> (0 <= An n)%Re) ->
  (0 <= sum_f_R0 An N)%Re.
Proof.
intros.
rewrite <- zero_sum_is_zero with (An:=(fun n:nat => 0%Re)) (n:=N).
+ apply sum_Rle.
  intros.
  apply H.
  by apply /leP.
+ by intros.
Qed.


Lemma Rle_neg_sum_with_Rlt_term_is_lt:
  forall (An:nat -> R) (Bn:nat -> R) (N:nat),
  (forall n0:nat, (n0 <= N)%nat -> (An n0 <= Bn n0)%Re) ->
  (exists (n1:nat), (n1 <= N)%nat /\ (An n1 < Bn n1)%Re) ->
  (sum_f_R0 An N < sum_f_R0 Bn N)%Re.
Proof.
intros.
elim H0.
intros n1 H1.
induction N as [|N'].
+ rewrite leqn0 in H1.
  destruct H1.
  assert(n1 = 0)%nat. {by apply /eqP. }
  by rewrite H3 in H2.
+ simpl.
  destruct (n1 == N'.+1) eqn:E.
  - assert (n1 = N'.+1). {by apply /eqP. }
    rewrite -H2.
    destruct H1.
    apply Rplus_le_lt_compat.
    * apply sum_Rle. intros. apply H.
      apply leq_trans with (m:=n) (p:=N'.+1) (n:=N').
      ++ by apply /leP.
      ++ apply leqnSn.
    * by [].
  - apply Rplus_lt_le_compat.
    * apply IHN'.
      ++ intros. by apply H, leqW.
      ++ exists n1.
         destruct H1.
         split.
         -- assert(n1 < N'.+1)%nat.
            {rewrite ltn_neqAle. apply /andP.
            split.
            ** by rewrite E.
            ** by [].
            }
            by rewrite -ltnS.
         -- by [].
      ++ destruct H1.
         split.
         -- assert(n1 < N'.+1)%nat.
            {rewrite ltn_neqAle. apply /andP.
            split.
            ** by rewrite E.
            ** by [].
            }
            by rewrite -ltnS.
         -- by [].
    * specialize (H N'.+1).
      apply H, ltnSn.
Qed.

 
Lemma non_neg_sum_with_pos_term_is_pos:
  forall (An:nat -> R) (N:nat),
  (forall n0:nat, (n0 <= N)%nat -> (0 <= An n0)%Re) ->
  (exists (n1:nat), (n1 <= N)%nat /\ (0 < An n1)%Re) ->
  (0 < sum_f_R0 An N)%Re.
Proof.
intros.
elim H0.
intros n1 H1.
induction N as [|N'].
+ rewrite leqn0 in H1.
  destruct H1.
  assert(n1 = 0)%nat. {by apply /eqP. }
  by rewrite H3 in H2.
+ simpl.
  destruct (n1 == N'.+1) eqn:E.
  - assert (n1 = N'.+1). {by apply /eqP. }
    rewrite -H2.
    destruct H1.
    apply Rplus_le_lt_0_compat.
    * apply sum_Rle_0. intros. apply H.
      apply leq_trans with (m:=n) (p:=N'.+1) (n:=N').
      ++ by [].
      ++ apply leqnSn.
    * by [].
  - apply Rplus_lt_le_0_compat.
    * apply IHN'.
      ++ intros. by apply H, leqW.
      ++ exists n1.
         destruct H1.
         split.
         -- assert(n1 < N'.+1)%nat.
            {rewrite ltn_neqAle. apply /andP.
            split.
            ** by rewrite E.
            ** by [].
            }
            by rewrite -ltnS.
         -- by [].
      ++ destruct H1.
         split.
         -- assert(n1 < N'.+1)%nat.
            {rewrite ltn_neqAle. apply /andP.
            split.
            ** by rewrite E.
            ** by [].
            }
            by rewrite -ltnS.
         -- by [].
    * specialize (H N'.+1).
      apply H, ltnSn.
Qed.

Lemma lim_is_0_or_1:
forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R) (j:D) (L:Rbar),
F_total_malicious mal init A w /\ 
(0 < F + 1 <= #|D|)%N /\
wts_well_behaved A mal init w /\
(exists S1 S2 : {set D}, 
  S1 \proper Vertex /\ 
  (0 < #|S1|)%N /\
  S2 \proper Vertex /\ 
  (0 < #|S2|)%N /\ 
  [disjoint S1 & S2] /\
  (#|Xi_S_r S1 (F + 1)| != #|S1|) /\ 
  (#|Xi_S_r S2 (F + 1)| != #|S2|) /\
  (F + 1 > #|Xi_S_r S1 (F + 1)| + #|Xi_S_r S2 (F + 1)|)%N /\
  A = (fun (i:D) => i \in (Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1))) /\
  mal = (fun (t:nat) => (fun (j:D) => if j \in S1 then 0 else 1))%Re /\
  init = (fun j : D => if j \in S1 then 0 else if j \notin S2 then (1 / 2)%Re else 1)%Re /\
  j \in S1 /\ 
  Adversary A = Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1) /\
  j \in Normal A) ->
((is_lim_seq ((x mal init A w)^~ j) L) <-> L = 0)%Re.
Proof.
intros.
destruct H. destruct H0. destruct H1.
elim H2. intros S1 H3. elim H3. intros S2 H4.
destruct H4. destruct H5. destruct H6. destruct H7. destruct H8.
destruct H9. destruct H10. destruct H11. destruct H12. destruct H13.
destruct H14. destruct H15. destruct H16.
assert(forall (q:nat) (l:D),
(l \in S1 -> x mal init A w q l = 0) /\
(l \notin S1 -> x mal init A w q l > 0))%Re.
{induction q as [|q' IHq'].
+ intros.
  split.
  - intro. simpl.
    destruct (A l) eqn:E.
    * by rewrite H13 H18.
    * by rewrite H14 H18.
  - intro. simpl.
    assert(l \in S1 = false). {by destruct (l \in S1). }
    destruct (A l) eqn:E.
    * rewrite H13 H19. nra.
    * rewrite H14 H19. destruct (l \in S2) eqn:E0.
      ++ simpl. nra.
      ++ simpl. nra.
+ intro.
  destruct (A l) eqn:E0.
  - split.
    * intro. by rewrite /= E0 H13 H18.
    * intro. assert(l \in S1 = false). {by destruct (l \in S1). }
       rewrite /= E0 H13 H19. nra.
  - split.
    * intro. rewrite /= E0.
      apply sum_eq_R0.
      intros v H19.
      apply Rmult_eq_0_compat.
      left.
      rewrite H12 in_set in E0.
      apply negbT in E0.
      assert(~~ (l \in Xi_S_r S1 (F + 1)) /\ ~~ (l \in Xi_S_r S2 (F + 1))).
      {by apply /norP. }
      destruct H20.
      rewrite in_set negb_and H18 /= -ltnNge in H20.
      assert(forall l0:D, l0 \in in_neighbor l :\: S1 ->
      x mal init A w q' l0 > 0)%Re.
      {intros.
      rewrite inE in H22.
      destruct (l0 \notin S1) eqn:E1.
      ++ specialize (IHq' l0).
         destruct IHq'.
         by apply H24 in E1.
      ++ by simpl in H22.
      }
      assert(in_neighbor l :\: S1 = 
      [set l0:D | l0 \in in_neighbor l &
      (Rgt_dec (x mal init A w q' l0) 0)%Re]).
      {apply eq_finset.
      intro l0.
      destruct (l0 \notin S1) eqn:E1.
      ++ specialize (IHq' l0).
         destruct IHq'.
         apply H24 in E1.
         destruct Rgt_dec.
         -- by rewrite andb_true_r /=.
         -- by [].
      ++ specialize (IHq' l0).
         destruct IHq'.
         assert(l0 \in S1). {by destruct (l0 \in S1). }
         apply H23 in H25. rewrite H25 /=.
         assert(0 <> 1)%Re. {by lra. }
         assert(0 != 1)%Re.
         {unfold negb.
         destruct (0 == 1)%Re eqn:E2.
         -- assert(0 = 1)%Re. {by apply /eqP. } by [].
         -- by [].
         }
         destruct (Rgt_dec 0 1)%Re eqn:E2.
         -- nra.
         -- destruct (Rgt_dec 0 0)%Re.
            ** nra.
            ** by rewrite /= andb_false_r.
       }
       rewrite H23 in H20.
       remember (incl_neigh_minus_extremes l (x mal init A w q')) as incl.
       assert(forall (l0:D), Rgt_dec (x mal init A w q' l0) 0 \/
       x mal init A w q' l0 == 0).
       {intros.
       destruct (l0 \in S1) eqn:E1.
       ++ right. apply /eqP.
          specialize (IHq' l0).
          destruct IHq'.
          by apply H24 in E1.
       ++ left. apply /eqP.
          assert(l0 \notin S1).
          {by rewrite E1. }
          specialize (IHq' l0).
          destruct IHq'.
          apply H26 in H24.
          by destruct Rgt_dec.
       }
       assert(G:forall l0 : D,
       Rgt_dec (x mal init A w q' l0) 0 \/
       x mal init A w q' l0 == 0).
       {by []. }
       specialize (H24 (last (head l incl) (behead incl))).
       destruct H24.
       ++ destruct (#|R_i_greater_than mal init A w l q'| < F)%N eqn:E1.
          -- apply card_R_i_gt_lt_F_exchange_last in E1.
             ** rewrite -Heqincl in E1.
                 assert(x mal init A w q' (last (head l incl) (behead incl)) > 0)%Re.
                 {by destruct Rgt_dec. }
                 rewrite E1 in H25.
                 specialize (IHq' l).
                 destruct IHq'.
                 apply H26 in H18.
                 rewrite H18 in H25.
                 nra.
             ** by [].
          -- assert(#|R_i_greater_than mal init A w l q'| == F)%N.
             {rewrite eqn_leq. apply /andP. split.
             ** apply R_i_gt_bounded.
             ** assert((#|R_i_greater_than mal init A w l q'| < F)%N -> false).
                {intros. by rewrite H25 in E1. }
                by apply contraNleq in H25.
             }
             assert(R_i_greater_than mal init A w l q' \subset
             (finset (fun l0 : D => (l0 \in in_neighbor l) &&
             (Rgt_dec (x mal init A w q' l0) 0%Re)))).
             {apply /subsetP. unfold sub_mem. intros k H26.
             rewrite in_set. rewrite in_set mem_sort mem_enum in_setU in H26.
             destruct (k == l) eqn:E2.
             ** assert(k = l). {by apply /eqP. }
                specialize (IHq' l). destruct IHq'. apply H28 in H18.
                assert(x mal init A w q' k = 0)%Re. {by rewrite -H27 in H18. }
                rewrite H18 H30 in H26.
                destruct Rgt_dec in H26.
                +++ assert(~(0 > 0)%Re). {by apply Rgt_irrefl. }
                    by [].
                +++ by simpl in H26.
             ** assert((k \in [set l]) = false).
                {destruct (k \in [set l]) eqn:E3.
                +++ by rewrite in_set1 E2 in E3.
                +++ by [].
                }
                rewrite H27 orb_false_r in H26.
                assert(k \in in_neighbor l). {by apply andb_triple_inject_right in H26. }
                assert(x mal init A w q' l = 0)%Re.
                {specialize (IHq' l). destruct IHq'. by apply H29 in H18. }
                rewrite H29 in H26.
                assert(Rgt_dec (x mal init A w q' k) 0).
                {by apply andb_triple_inject_left in H26. }
                by rewrite H30 H28.
             }
             assert(last (head l incl) (behead incl) \in
             finset (fun l0 : D => (l0 \in in_neighbor l) &&
             Rgt_dec (x mal init A w q' l0) 0)).
             {rewrite in_set. apply /andP. split.
             ** assert(last (head l incl) (behead incl) \in incl).
                {rewrite -> list_dissect with (i:=l) (l:=incl) at 3.
                +++ apply mem_last.
                +++ rewrite Heqincl. apply incl_not_empty.
                }
                rewrite -> Heqincl in H27 at 3.
                apply incl_subset_inclusive_neighbors in H27.
                rewrite mem_sort mem_enum in_setU in H27.
                destruct (last (head l incl) (behead incl) \in
                [set l]) eqn:E2.
                +++ rewrite in_set1 in E2.
                    assert(last (head l incl) (behead incl) != l).
                    {assert((x mal init A w q' (last (head l incl) (behead incl))
                    <> x mal init A w q' l)%Re).
                    {destruct Rgt_dec.
                    --- assert(x mal init A w q' l = 0)%Re.
                        {specialize (IHq' l). destruct IHq'. by apply H28 in H18. }-
                        simpl in H24. rewrite -H28 in r.
                        by apply Rgt_not_eq in r.
                    --- by simpl in H24.
                    }
                    assert(last (head l incl) (behead incl) = l).
                    {by apply /eqP. }
                    by rewrite <- H29 in H28 at 2.
                    }
                    by rewrite E2 in H28.
                +++ by rewrite orb_false_r in H27.
             ** by [].
             }
             assert(R_i_greater_than mal init A w l q' \proper
             finset (fun l0 : D => (l0 \in in_neighbor l) &&
             Rgt_dec (x mal init A w q' l0) 0)).
             {apply /properP. split.
             ** by [].
             ** exists (last (head l incl) (behead incl)).
                +++ by [].
                +++ apply R_i_gt_and_incl_disjoint.
                    rewrite Heqincl.
                    apply last_incl_in_incl.
             }
             assert(#|R_i_greater_than mal init A w l q'| = F)%N.
             {by apply /eqP. }
             rewrite properEcard H26 /= H29 in H28.
             apply ltn_geF in H28.
             rewrite -ltnS in H28.
             by rewrite addn1 H28 in H20.
       ++ destruct (v == (size incl).-1)%N eqn:E1.
          -- assert(v = (size incl).-1)%N. {by apply /eqP. }
             assert((last (head l incl) (behead incl)) = (nth l incl v)).
             {rewrite H25 -size_behead. rewrite -> list_dissect with (l:= incl) (i:=l) at 3.
             ** by rewrite (last_nth l).
             ** rewrite Heqincl. apply incl_not_empty.
             }
             rewrite -H26. by apply /eqP.
          -- assert(x mal init A w q'
             (last (head l incl) (behead incl)) = 0).
             {by apply /eqP. }
             assert(x mal init A w q' (nth l incl v) <=
             x mal init A w q'
             (last (head l incl) (behead incl)))%Re.
             {assert(v <= (size incl).-1)%N.
             {rewrite -subn1. by apply /leP. }
             assert((size incl).-1.+1 = size incl)%N.
             {apply ltn_predK with (m:=0%N).
             rewrite Heqincl. apply size_incl_not_0.
             }
             assert(v < size incl)%N. {by rewrite -ltnS H27 in H26. }
             apply lemma_1.incl_sorted
             with (t:=q') (i:=l) (mal:=mal) (init:=init) (A:=A) (w:=w).
             ** rewrite -Heqincl. by apply mem_nth.
             ** rewrite -Heqincl (last_nth (head l incl)) -list_dissect.
                +++ rewrite size_behead. apply mem_nth.
                    rewrite ltn_predL Heqincl. apply size_incl_not_0.
                +++ rewrite Heqincl. apply incl_not_empty.
             ** rewrite -Heqincl (last_nth (head l incl)) -list_dissect.
                +++ assert(uniq incl).
                    {rewrite Heqincl. apply incl_uniq. }
                    rewrite index_uniq.
                    --- assert((v < size (behead incl))%N).
                        {by rewrite size_behead ltn_neqAle E1 H26. }
                        assert((size (behead incl) < size incl)%N).
                        {rewrite size_behead ltn_predL Heqincl.
                        apply size_incl_not_0.
                        }
                        by rewrite index_uniq.
                    --- by [].
                    --- by [].
                +++ rewrite Heqincl. apply incl_not_empty.
             }
             rewrite H25 in H26.
             assert(forall (l0:D), 0 <= x mal init A w q' l0)%Re.
             {intros. specialize (G l0).
             destruct G.
             ** assert(x mal init A w q' l0 > 0)%Re.
                {by destruct Rgt_dec. }
                nra.
             ** assert(x mal init A w q' l0 = 0)%Re.
                {by apply /eqP. }
                rewrite H28. nra.
             }
             specialize (H27 (nth l incl v)).
             by apply Rle_antisym.
    * intro. rewrite /= E0.
      remember (incl_neigh_minus_extremes l (x mal init A w q')) as incl.
      assert(exists (n0:nat), (n0 < size incl)%N /\
      x mal init A w q' (nth l incl n0) > 0)%Re.
      {assert(l \in incl).
      {rewrite Heqincl. apply i_in_incl. }
      assert(exists2 i, (i < size incl)%nat & nth l incl i = l).
      {by apply /nthP. }
      elim H20.
      intros n H21 H22.
      exists n.
      rewrite H22 /=.
      split.
      ++ by [].
      ++ specialize (IHq' l).
         destruct IHq'.
         by apply H24.
      }
      apply non_neg_sum_with_pos_term_is_pos.
      ++ intros.
         apply Rmult_le_pos.
         -- assert(forall (l0:D), (0 <= x mal init A w q' l0)%Re).
            {intros.
            destruct (l0 \in S1) eqn:E1.
            ** specialize (IHq' l0). destruct IHq'.
               apply H21 in E1. rewrite E1. nra.
            ** specialize (IHq' l0). destruct IHq'.
               assert(l0 \notin S1). {by rewrite E1. }
               apply H22 in H23. by apply Rge_le, Rgt_ge.
            }
            by specialize (H21 (nth l incl n0)).
         -- elim H1. intros a H21. destruct H21. destruct H22.
            specialize (H23 q' l).
            assert(l \in Normal A).
            {by rewrite !in_set E0. }
            destruct H23.  destruct H25.
            specialize (H25 (nth l incl n0)).
            apply Rle_trans with (r2:=a).
            ** apply Rlt_le, H21.
            ** apply H25. rewrite Heqincl. apply mem_nth.
               rewrite subn1 -ltnS prednK in H20.
               +++ by rewrite -Heqincl.
               +++ rewrite Heqincl. apply size_incl_not_0.
      ++ elim H19.
         intros n0 H21.
         exists n0.
         destruct H21.
         split.
         -- rewrite leq_subRL.
            ** by rewrite addnC addn1.
            ** rewrite Heqincl. apply size_incl_not_0.
         -- apply Rmult_lt_0_compat.
          ** by [].
          ** elim H1. intros a H22. destruct H22. destruct H23.
             specialize (H24 q' l).
             assert(l \in Normal A).
             {by rewrite !in_set E0. }
             destruct H24.  destruct H26.
             specialize (H26 (nth l incl n0)).
             apply Rlt_le_trans with (r2:=a).
             +++ by [].
             +++ apply H26. rewrite Heqincl. apply mem_nth.
                 by rewrite -Heqincl.
}
split.
+ intro.
  assert(forall (k:D), k \in S1 ->
  ((x mal init A w)^~ k) =1 (fun k => 0)).
  {intros k H20 t.
  specialize (H18 t k). destruct H18. by apply H18 in H20.
  }
  apply H20 in H15.
  apply functional_extensionality in H15.
  rewrite H15 in H19. apply is_lim_seq_unique in H19.
  by rewrite Lim_seq_const in H19.
+ intro.
  rewrite H19 is_lim_seq_Reals. unfold Un_cv.
  intros eps H20.
  exists 0%N.
  intros n H21.
  specialize (H18 n j). destruct H18. apply H18 in H15.
  rewrite H15. unfold R_dist.
  assert(0 - 0 = 0)%Re. {nra. }
  by rewrite H23 Rabs_R0.
Qed.

Lemma wts_gt_0:
forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R),
wts_well_behaved A mal init w ->
forall (i j:D) (t:nat), 
  j \in (incl_neigh_minus_extremes i (x mal init A w t)) ->
  (0 < w t (i,j))%Re.
Proof.
intros.
destruct H. destruct H. destruct H1.
specialize (H2 t i). destruct H2.
destruct H3.
apply Rlt_le_trans with (r2:=x).
+ by [].
+ by apply H3.
Qed.

Lemma normal_set_to_enum: forall (i:D) (A: D -> bool),
  i \in (Normal A) -> i \in enum (Normal A).
Proof.
intros.
assert ([set x | x \in enum (Normal A)] = (Normal A)).
{ apply set_enum. } rewrite -H0 in H.
by rewrite inE in H.
Qed.


Lemma x_bound: forall (i:D) (mal:nat -> D -> R) (init:D -> R) (A: D -> bool) (w:nat -> D*D -> R), 
  i \in (Normal A) ->  
  forall t : nat, (m mal init A w t <= x mal init A w t i <= M mal init A w t)%Re.
Proof.
intros. 
(** x t i <= Rmax (x t i) (M - (x t i))
    Rmin (x t i) (m - (x t i)) <= x t i
**)
split.
+ assert (m mal init A w t = -(bigmaxr 0 ((map (fun i:D => -(x mal init A w t i))) (enum (Normal A))))).
  { by rewrite /m. } rewrite H0.
  assert ( x mal init A w t i = (- (- (x mal init A w t i)))). 
  { rewrite -!RoppE. by rewrite Ropp_involutive. } rewrite H1.
  apply Ropp_le_contravar. rewrite -RoppE.
  assert ( nth 0%Re ((map (fun i:D => -(x mal init A w t i))) (enum (Normal A))) 
            (index i (enum (Normal A)))= 
                     (fun i:D => - (x mal init A w t i)) (nth key (enum (Normal A)) 
            (index i (enum (Normal A))))).
  { apply (@nth_map D key R 0%Re (fun i:D => -(x mal init A w t i)) (index i (enum (Normal A))) (enum (Normal A))).
    rewrite index_mem. by apply normal_set_to_enum.
  }
  assert ((- x mal init A w t i)%Re  = (fun i : D => - x mal init A w t i) (nth key (enum (Normal A))
          (index i (enum (Normal A))))).
  { assert ( i  = nth key (enum (Normal A)) (index i (enum (Normal A)))).
    { symmetry. by apply nth_index, normal_set_to_enum. }
    by rewrite [in LHS]H3.
  } rewrite H3. rewrite -H2.
  apply /RleP. 
  apply (@bigmaxr_ler _ 0%Re [seq - x mal init A w t i0 | i0 <- enum (Normal A)] (index i (enum (Normal A))) ). 
  rewrite size_map. rewrite index_mem. by apply normal_set_to_enum.
+ assert (M mal init A w t = bigmaxr 0 (map (x mal init A w t) (enum (Normal A)))).
  { by rewrite /M. } rewrite H0. apply normal_set_to_enum in H.
  clear H0.
  assert ( nth 0%Re ((map (fun i:D => (x mal init A w t i))) (enum (Normal A))) 
            (index i (enum (Normal A)))= 
                     (fun i:D => (x mal init A w t i)) (nth key (enum (Normal A)) 
            (index i (enum (Normal A))))).
  { apply (@nth_map D key R 0%Re (fun i:D => (x mal init A w t i)) (index i (enum (Normal A))) (enum (Normal A))).
    by rewrite index_mem. 
  }
  assert ((x mal init A w t i)%Re  = (fun i : D => x mal init A w t i) (nth key (enum (Normal A))
          (index i (enum (Normal A))))).
  { assert ( i  = nth key (enum (Normal A)) (index i (enum (Normal A)))).
    { symmetry. by apply nth_index. }
    by rewrite [in LHS]H1.
  } rewrite H1. rewrite -H0.
  apply /RleP.
  apply (@bigmaxr_ler _ 0%Re [seq x mal init A w t i0 | i0 <- enum (Normal A)] (index i (enum (Normal A))) ). 
  by rewrite size_map index_mem.
Qed.

Fixpoint x_w (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (two_t:nat) (t:nat)  :=
match two_t with
  |O => ((fun (i:D) =>
          if (A i) then mal 0%nat i else init i),
          let x0:= (fun (i:D) =>
          if (A i) then mal 0%nat i else init i) in
          fun (i_j:D*D) =>
          let incl_0 := incl_neigh_minus_extremes (fst i_j) x0 in
          if (snd i_j \in incl_0) then (/ INR (size incl_0))%Re else 0%Re
          )
  |S two_t' => match (two_t %% 2 == 0)%N with
      |true => (match t with
        |O => ((fun (i:D) =>
          if (A i) then mal 0%nat i else init i),
          let x0:= (fun (i:D) =>
          if (A i) then mal 0%nat i else init i) in
          fun (i_j:D*D) =>
          let incl_0 := incl_neigh_minus_extremes (fst i_j) x0 in
          if (snd i_j \in incl_0) then (/ INR (size incl_0))%Re else 0%Re
          )
        |S t' => let x_w_t_t_minus_1 := x_w mal init A two_t' t' in
          let xt := (fst x_w_t_t_minus_1) in
          let wt_minus_1 := (snd x_w_t_t_minus_1) in
          let wt := (fun (i_j:D*D) =>
          let incl_t := incl_neigh_minus_extremes (fst i_j) xt in
          if (snd i_j \in incl_t) then (/ INR (size incl_t))%Re else 0%Re
          )
          in
          (xt, wt)
      end)
      |false => (match t with
        |O => let x_w_0_0 := x_w mal init A two_t' 0%nat in
          let x0 := (fst x_w_0_0) in
          let w0 := (snd x_w_0_0) in
          let x1 :=  (fun (i:D) =>
          match (A i) with
            |true => mal 1%N i
            |false => let incl_0 := incl_neigh_minus_extremes i x0 in
              sum_f_R0 (fun (n:nat) => ((x0 (nth i incl_0 n)) *
              (w0 (i, (nth i incl_0 n)))%Re))
              ((size incl_0).-1)
          end
          )
          in
          (x1, w0)
        |S t' => let x_w_t_t := x_w mal init A two_t' t in
          let xt := (fst x_w_t_t) in
          let wt := (snd x_w_t_t) in
          let xt_plus_1 := (fun (i:D) =>
          match (A i) with
            |true => mal t.+1 i
            |false => let incl_t := incl_neigh_minus_extremes i xt in
              sum_f_R0 (fun (n:nat) => ((xt (nth i incl_t n)) *
              (wt (i, (nth i incl_t n))))%Re)
              ((size incl_t).-1)
          end
          )
          in
          (xt_plus_1, wt)
        end)
  end
end.

Lemma trivial_x_w_applied:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (two_t:nat) (t:nat),
x_w mal init A two_t t =
match two_t with
  |O => ((fun (i:D) =>
          if (A i) then mal 0%nat i else init i),
          let x0:= (fun (i:D) =>
          if (A i) then mal 0%nat i else init i) in
          fun (i_j:D*D) =>
          let incl_0 := incl_neigh_minus_extremes (fst i_j) x0 in
          if (snd i_j \in incl_0) then (/ INR (size incl_0))%Re else 0%Re
          )
  |S two_t' => match (two_t %% 2 == 0)%N with
      |true => (match t with
        |O => ((fun (i:D) =>
          if (A i) then mal 0%nat i else init i),
          let x0:= (fun (i:D) =>
          if (A i) then mal 0%nat i else init i) in
          fun (i_j:D*D) =>
          let incl_0 := incl_neigh_minus_extremes (fst i_j) x0 in
          if (snd i_j \in incl_0) then (/ INR (size incl_0))%Re else 0%Re
          )
        |S t' => let x_w_t_t_minus_1 := x_w mal init A two_t' t' in
          let xt := (fst x_w_t_t_minus_1) in
          let wt_minus_1 := (snd x_w_t_t_minus_1) in
          let wt := (fun (i_j:D*D) =>
          let incl_t := incl_neigh_minus_extremes (fst i_j) xt in
          if (snd i_j \in incl_t) then (/ INR (size incl_t))%Re else 0%Re
          )
          in
          (xt, wt)
      end)
      |false => (match t with
        |O => let x_w_0_0 := x_w mal init A two_t' 0%nat in
          let x0 := (fst x_w_0_0) in
          let w0 := (snd x_w_0_0) in
          let x1 :=  (fun (i:D) =>
          match (A i) with
            |true => mal 1%N i
            |false => let incl_0 := incl_neigh_minus_extremes i x0 in
              sum_f_R0 (fun (n:nat) => ((x0 (nth i incl_0 n)) *
              (w0 (i, (nth i incl_0 n)))%Re))
              ((size incl_0).-1)
          end
          )
          in
          (x1, w0)
        |S t' => let x_w_t_t := x_w mal init A two_t' t in
          let xt := (fst x_w_t_t) in
          let wt := (snd x_w_t_t) in
          let xt_plus_1 := (fun (i:D) =>
          match (A i) with
            |true => mal t.+1 i
            |false => let incl_t := incl_neigh_minus_extremes i xt in
              sum_f_R0 (fun (n:nat) => ((xt (nth i incl_t n)) *
              (wt (i, (nth i incl_t n))))%Re)
              ((size incl_t).-1)
          end
          )
          in
          (xt_plus_1, wt)
        end)
  end
end.
Proof.
intros.
destruct two_t as [|two_t'].
+ by simpl.
+ by simpl.
Qed.

Lemma trivial_x_w:

x_w =
fix x_w
             (mal : nat -> D -> R) (init : D -> R)
             (A : D -> bool) (two_t t : nat) {struct two_t} :
               (D -> R) * (D * D -> R) :=
match two_t with
  |O => ((fun (i:D) =>
          if (A i) then mal 0%nat i else init i),
          let x0:= (fun (i:D) =>
          if (A i) then mal 0%nat i else init i) in
          fun (i_j:D*D) =>
          let incl_0 := incl_neigh_minus_extremes (fst i_j) x0 in
          if (snd i_j \in incl_0) then (/ INR (size incl_0))%Re else 0%Re
          )
  |S two_t' => match (two_t %% 2 == 0)%N with
      |true => (match t with
        |O => ((fun (i:D) =>
          if (A i) then mal 0%nat i else init i),
          let x0:= (fun (i:D) =>
          if (A i) then mal 0%nat i else init i) in
          fun (i_j:D*D) =>
          let incl_0 := incl_neigh_minus_extremes (fst i_j) x0 in
          if (snd i_j \in incl_0) then (/ INR (size incl_0))%Re else 0%Re
          )
        |S t' => let x_w_t_t_minus_1 := x_w mal init A two_t' t' in
          let xt := (fst x_w_t_t_minus_1) in
          let wt_minus_1 := (snd x_w_t_t_minus_1) in
          let wt := (fun (i_j:D*D) =>
          let incl_t := incl_neigh_minus_extremes (fst i_j) xt in
          if (snd i_j \in incl_t) then (/ INR (size incl_t))%Re else 0%Re
          )
          in
          (xt, wt)
      end)
      |false => (match t with
        |O => let x_w_0_0 := x_w mal init A two_t' 0%nat in
          let x0 := (fst x_w_0_0) in
          let w0 := (snd x_w_0_0) in
          let x1 :=  (fun (i:D) =>
          match (A i) with
            |true => mal 1%N i
            |false => let incl_0 := incl_neigh_minus_extremes i x0 in
              sum_f_R0 (fun (n:nat) => ((x0 (nth i incl_0 n)) *
              (w0 (i, (nth i incl_0 n)))%Re))
              ((size incl_0).-1)
          end
          )
          in
          (x1, w0)
        |S t' => let x_w_t_t := x_w mal init A two_t' t in
          let xt := (fst x_w_t_t) in
          let wt := (snd x_w_t_t) in
          let xt_plus_1 := (fun (i:D) =>
          match (A i) with
            |true => mal t.+1 i
            |false => let incl_t := incl_neigh_minus_extremes i xt in
              sum_f_R0 (fun (n:nat) => ((xt (nth i incl_t n)) *
              (wt (i, (nth i incl_t n))))%Re)
              ((size incl_t).-1)
          end
          )
          in
          (xt_plus_1, wt)
        end)
  end
end.

Proof.
by unfold x_w.
Qed.

Definition x_aux (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i:D) :=
(x_w mal init A (2*t)%N t).1 i.


Lemma x_aux_trivial:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i:D),
x_aux mal init A t i = (x_w mal init A (2*t)%N t).1 i.
Proof.
intros. by unfold x_aux.
Qed.

Definition w_aux (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i_j:D*D) :=
(x_w mal init A (2*t)%N t).2 i_j.


Lemma w_aux_trivial:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i_j:D*D),
w_aux mal init A t i_j = (x_w mal init A (2*t)%N t).2 i_j.
Proof.
intros. by unfold w_aux.
Qed.


Lemma mod_equiv:
forall (t:nat),
(((t + (t + 0)%coq_nat.+1)%coq_nat.+1) %% 2)%nat == 0%nat.
Proof.
intros.
rewrite plusE. assert((t + (t + 0).+1).+1 = (2 * t).+2).
{by rewrite addn0 addnS addnn mul2n. }
by rewrite H /= -addn2 modnDr modnMr.
Qed.

Lemma arith_eqn:
forall (t:nat),
((t + (t + 0)%coq_nat.+1)%coq_nat = (2*t).+1)%N.
Proof.
intros. by rewrite plusE addn0 addnS addnn mul2n.
Qed.


Lemma simpl_pair_fst:
forall (T1 T2: Type) (a:T1) (b:T2),
(a, b).1 = a.
Proof.
by [].
Qed.

Lemma simpl_pair_snd:
forall (T1 T2: Type) (a:T1) (b:T2),
(a, b).2 = b.
Proof.
by [].
Qed.


Lemma x_aux_equiv:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat),
((x_w mal init A (2*t)%N t).1 =
x mal init A (fun (t:nat) => (x_w mal init A (2*t)%N t).2) t)%Re.
Proof.
intros mal init A. induction t as [|t' IHt'].
+ intros. by simpl.
+ intros. assert(0%nat == 0%nat). {by apply /eqP. }
  rewrite /= plusE addn0 addnS addnn -muln2 -addn2 modnMDl modnn H /=.
  assert(((t' * 2).+1 %% 2)%nat == 0%nat =false).
  {by rewrite -addn1 modnMDl modn_small. }
  rewrite H0. apply functional_extensionality. intro i.
  destruct t' as [|t''].
  + by rewrite subn1 /=.
  + rewrite simpl_pair_fst. destruct (A i).
    - by [].
    - by rewrite -!IHt' subn1 mulnC.
Qed.

Lemma sum_f_R0_big_equiv (F:nat -> R) (n:nat):
  sum_f_R0 F n = \big[+%R/0]_(j<n.+1) F j.
Proof.
induction n.
+ by rewrite /sum_f_R0 big_ord_recr big_ord0 //= add0r.
+ simpl. rewrite big_ord_recr //= IHn. by rewrite RplusE.
Qed.

Lemma x_w_repeat_x:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (q:nat),
(x_w mal init A (2 * q).+1 q).1 =
(x_w mal init A (2 * q.+1) q.+1).1.
Proof.
intros mal init A.
induction q as [|q' IHq'].
+ simpl. apply functional_extensionality. intro k.
  by destruct (A k).
+ unfold x_w at 1. rewrite -trivial_x_w -!IHq'.
  assert(((2 * q'.+1).+1 %% 2)%nat == 0%nat = false).
  {by rewrite -addn1 mulnC modnMDl modn_small. }
  rewrite H simpl_pair_fst.
  apply functional_extensionality. intro k.
  assert(((q' + (q' + 0)%coq_nat.+2)%coq_nat.+2 %% 2)%nat == 0%nat).
  {by rewrite plusE addn0 -addn2 modnDr -addn2 addnA modnDr addnn -muln2 modnMl. }
  assert(((q' + (q' + 0)%coq_nat.+2)%coq_nat.+1 %% 2)%nat == 0%nat = false).
  {by rewrite plusE addn0 -addn2 addnA addnn -addn1 -addnC addnA modnDr -muln2 addnC modnMDl modn_small. }
  destruct (A k) eqn:E.
  - by rewrite /= H0 H1 /= E.
  - assert(((2 * q').+1 %% 2)%nat == 0%nat = false).
    {by rewrite -addn1 mulnC modnMDl modn_small. }
    assert(q'.+2 = (q' + 1).+1). {by rewrite addn1. }
    assert(((q' + 1 + (q' + 1 + 0)%coq_nat.+1)%coq_nat.+1 %% 2)%nat == 0%nat).
    {by rewrite plusE addn0 addn1 addSn -addn2 modnDr -addn2 addnA modnDr addnn -muln2 modnMl. }
    assert((q' + (q' + 0)%coq_nat.+2)%coq_nat = (2 * q'.+1))%N.
    {by rewrite plusE addn0 -addSnnS addnn -muln2 mulnC. }
    by rewrite H3 /= H4 simpl_pair_fst addn1 /= H5 IHq' H simpl_pair_fst E.
Qed.

Lemma wts_equiv_one_over_size_incl:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t n:nat) (i:D),
(n < (size (incl_neigh_minus_extremes i (x mal init A
            (fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t))))%N ->
(x_w mal init A (2 * t) t).2 (i, nth i (incl_neigh_minus_extremes i
    (x mal init A
    (fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t)) n) =
(/ INR (size (incl_neigh_minus_extremes i (x mal init A
(fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t))))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A
(fun t0 : nat => [eta (x_w mal init A (2 * t0) t0).2]) t)) as incl.
destruct t as [|t'].
+ simpl in Heqincl.
  assert(nth i incl n \in incl).
  {by apply mem_nth. }
  by rewrite /= -Heqincl H0.
+ assert(((t' + (t' + 0)%coq_nat.+1)%coq_nat.+1 %% 2)%nat == 0%nat).
  {by rewrite plusE addn0 -addSn addnn -muln2 modnMl. }
  assert((t' + (t' + 0)%coq_nat.+1)%coq_nat = (2*t').+1)%N.
  {by rewrite plusE addn0 addnS addnn -muln2 mulnC. }
  rewrite /= H0 H1 x_w_repeat_x !simpl_pair_snd simpl_pair_fst.
  assert(nth i incl n \in incl).
  {by apply mem_nth. }
  by rewrite x_aux_equiv -Heqincl H2.
Qed.

Lemma sum_of_1_over_incl_is_equiv_wts:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i:D),
(sum_f_R0 (fun n : nat => (x_w mal init A (2 * t) t).2
(i, nth i (incl_neigh_minus_extremes i (x mal init A
(fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t)) n))%Re
(size (incl_neigh_minus_extremes i (x mal init A
(fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t)) - 1) =
sum_f_R0 (fun n : nat => (/ INR (size (incl_neigh_minus_extremes i
(x mal init A
(fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t))))%Re)
(size (incl_neigh_minus_extremes i (x mal init A
(fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t)) - 1))%Re.
Proof.
intros. remember (incl_neigh_minus_extremes i (x mal init A
(fun t0 : nat => [eta (x_w mal init A (2 * t0) t0).2]) t)) as incl.
apply PartSum.sum_eq. intros. rewrite Heqincl.
apply wts_equiv_one_over_size_incl. rewrite -Heqincl.
assert((size incl).-1.+1 = size incl).
{apply prednK. rewrite Heqincl. apply size_incl_not_0. }
assert((i0 <= size incl - 1)%nat). {by apply /leP. }
by rewrite subn1 -ltnS H0 in H1.
Qed.

Lemma sum1_size_R J (r : seq J) :
\sum_(j <- r) 1%Re = INR (size r).
Proof.
induction r as [|h t].
+ by rewrite /= big_nil.
+ rewrite big_cons IHt. simpl.
  destruct (size t)%N.
  - by rewrite /= addr0.
  - by rewrite RplusE addrC.
Qed.

Lemma sum_of_inv_incl_is_1:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i:D),
(sum_f_R0 (fun n : nat =>
(/ INR (size (incl_neigh_minus_extremes i
(x mal init A
(fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t))))%Re)
(size (incl_neigh_minus_extremes i (x mal init A
(fun t : nat => [eta (x_w mal init A (2 * t) t).2]) t)) - 1) =
1)%Re.
Proof.
intros. remember (incl_neigh_minus_extremes i (x mal init A
(fun t0 : nat => [eta (x_w mal init A (2 * t0) t0).2]) t)) as incl.
rewrite sum_f_R0_big_equiv.
assert((/ INR (size incl))%Re = (1 * / INR (size incl))%Re).
{by rewrite Rmult_1_l. }
rewrite H.
rewrite -big_distrl H /= Rmult_1_l.
rewrite sum1_size_R /=.
unfold index_enum, index_enum_key, locked_with.
rewrite -enumT -cardE card_ord subn1 prednK.
+ apply Rinv_r, Rgt_not_eq, lt_0_INR. apply /ltP.
  rewrite Heqincl. apply size_incl_not_0.
+ rewrite Heqincl. apply size_incl_not_0.
Qed.

Lemma inv_size_incl_large:
forall (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i:D),
(1 < INR #|D|)%Re -> (/ INR #|D| <=
/ INR (size (incl_neigh_minus_extremes i (x mal init A
(fun t : nat => (x_w mal init A (2 * t) t).2) t))))%Re.
Proof.
intros.
remember (incl_neigh_minus_extremes i (x mal init A
(fun t0 : nat => (x_w mal init A (2 * t0) t0).2) t)) as incl.
destruct ((size incl) == #|D|)%N eqn:E.
+ assert((size incl) = #|D|)%N. {by apply /eqP. }
  rewrite H0. by right.
+ left. apply Rinv_1_lt_contravar.
  - assert(1 = INR 1)%Re. {by []. }
    rewrite H0. apply le_INR. apply /leP. rewrite Heqincl.
    apply size_incl_not_0.
  - apply lt_INR. apply /ltP.
    rewrite ltn_neqAle E /=.
    assert((size incl) = #|incl|)%N.
    {symmetry. apply /card_uniqP. rewrite Heqincl. apply incl_uniq. }
    rewrite H0. apply max_card.
Qed.

Lemma necessity_proof:
nonempty_nontrivial_graph ->
(~ r_s_robustness (F + 1) (F + 1) ->
 ~ (forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) (w:nat -> D*D -> R),
      wts_well_behaved A mal init w ->
      Resilient_asymptotic_consensus A mal init w)).
Proof.
intro G. intros. unfold r_s_robustness in H.
unfold Resilient_asymptotic_consensus. apply nand_temp in H.
rewrite G in H. destruct H.
+ by [].
+ apply -> not_implies_as_and in H. destruct H.
  apply not_all_ex_not in H0. elim H0. clear H0. intros S1 H0.
  apply not_all_ex_not in H0. elim H0. clear H0. intros S2 H0.
  apply -> not_implies_as_and in H0. destruct H0.
  apply -> not_implies_as_and in H1. destruct H1.
  apply -> not_implies_as_and in H2. destruct H2.
  assert(#|Xi_S_r S1 (F + 1)| != #|S1| /\
  #|Xi_S_r S2 (F + 1)| != #|S2| /\
  (#|Xi_S_r S1 (F + 1)| + #|Xi_S_r S2 (F + 1)| < F + 1)%N).
  {rewrite -andb_triple_prop.
  replace (#|Xi_S_r S1 (F + 1)| + #|Xi_S_r S2 (F + 1)| < F + 1)%N with
  (~~(F + 1 <= #|Xi_S_r S1 (F + 1)| + #|Xi_S_r S2 (F + 1)|)%N).
  + rewrite -nandb_triple. by apply /negP.
  + by rewrite ltnNge.
  }
  clear H3. destruct H4. destruct H4. apply ex_not_not_all.
  remember (fun (i:D) => i \in (Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1))) as A.
  exists A. apply ex_not_not_all.
  remember (fun (t:nat) => (fun (j:D) => if j \in S1 then 0 else 1))%Re as mal.
  exists mal. apply ex_not_not_all.
  remember (fun (j:D) => if j \in S1 then 0 else if j \notin S2 then (1/2)%Re else 1)%Re as init.
  exists init. apply ex_not_not_all. exists (w_aux mal init A).
  assert(wts_well_behaved A mal init (w_aux mal init A)).
  {unfold wts_well_behaved. exists ( /INR (#|D|))%Re.
  assert(1 < INR #|D|)%Re.
  {apply lt_1_INR. by apply /ltP. }
  split.
  + apply Rinv_0_lt_compat, lt_0_INR. apply /ltP.
    assert(0 < F + 1 /\ F + 1 <= #|D|)%N.
    {by apply /andP. }
    destruct H7. by apply ltn_leq_trans with (F+1)%N.
  + split.
    - rewrite -Rinv_1. apply Rinv_1_lt_contravar.
      * by right.
      * by [].
    - unfold w_aux, x_aux.
      induction t as [|t'].
      * intro. split.
        ++ intros. simpl. simpl in H7.
           assert(j \in incl_neigh_minus_extremes i
           (fun i0 : D => if A i0 then mal 0%nat i0 else init i0) = false).
           {destruct (j \in incl_neigh_minus_extremes i
           (fun i0 : D => if A i0 then mal 0%nat i0 else init i0)) eqn:E.
           + by rewrite E in H7.
           + by [].
           }
           by rewrite H8.
        ++ split.
            -- intros. simpl in H7. rewrite /= H7.
               assert(((x mal init A (fun t : nat =>
               (x_w mal init A (2 * 0) 0).2) 0) =
               (fun i0 : D => if A i0 then mal 0%nat i0 else init i0))).
               {by []. }
               rewrite -H8. by apply inv_size_incl_large with (t:=0%N).
            -- by rewrite sum_of_1_over_incl_is_equiv_wts sum_of_inv_incl_is_1.
      * intros. split.
        ++ intros. unfold w_aux. simpl.
           assert(0%nat == 0%nat). {by apply /eqP. }
           rewrite /= plusE addn0 addnS addnn -muln2 -addn2 modnMDl modnn H8 mulnC.
           rewrite !simpl_pair_snd simpl_pair_fst x_w_repeat_x.
           assert(j \in incl_neigh_minus_extremes i
           (x_w mal init A (2 * t'.+1) t'.+1).1 = false).
           {rewrite x_aux_equiv. by destruct (j \in incl_neigh_minus_extremes i
           (x mal init A (fun t : nat => (x_w mal init A (2 * t) t).2)
            t'.+1)).
           }
           by rewrite H9.
        ++ split.
           -- intros. rewrite /= mod_equiv /= arith_eqn x_w_repeat_x.
              rewrite x_aux_equiv H7. by apply inv_size_incl_large.
           -- by rewrite sum_of_1_over_incl_is_equiv_wts sum_of_inv_incl_is_1.
  }
  apply <- not_implies_as_and.
  assert(Adversary A =
  (Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1))).
  {rewrite HeqA. apply eq_finset. intro k. rewrite -in_setU.
  by destruct (k \in Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1)) eqn:E.
  }
  assert(Xi_S_r S1 (F + 1) \subset S1).
  {apply /subsetP. intros k H12. rewrite in_set in H12.
  by destruct (k \in S1) eqn:E.
  }
  assert(Xi_S_r S2 (F + 1) \subset S2).
  {apply /subsetP. intros k H13. rewrite in_set in H13.
  by destruct (k \in S2) eqn:E.
  }
  assert(Xi_S_r S1 (F + 1) \proper S1).
  {rewrite properEcard H8 /=.
  destruct (Xi_S_r S1 (F + 1) == S1) eqn:E0.
  + assert(Xi_S_r S1 (F + 1) = S1). {by apply /eqP. }
    rewrite H10 in H3.
    assert(#|S1| <> #|S1|). {by apply /eqP. }
    by [].
  + assert(Xi_S_r S1 (F + 1) \proper S1).
    {by rewrite properEneq H8 E0. }
    by apply proper_card.
  }
  assert(F_total_malicious mal init A (w_aux mal init A)).
  {split.
  + assert(#|Xi_S_r S1 (F + 1) :&: Xi_S_r S2 (F + 1)| = 0)%N.
    {apply /eqP.
    rewrite cards_eq0. apply /eqP. apply eq_finset.
    intro j. rewrite !in_set. destruct (j \in S1) eqn:E.
    + apply disjointFr with (x:=j) in H2.
      - by rewrite H2 /= andb_false_r.
      - by [].
    + by simpl.
    }
    unfold F_totally_bounded, F_total. rewrite H7. split.
    - rewrite properEcard subsetT /=.
      apply ltn_leq_trans with (n:=(F+1)%N) (p:=#|Vertex|)
      (m:=#|Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1)|).
      * assert(#|Xi_S_r S1 (F + 1) :&: Xi_S_r S2 (F + 1)| = 0)%N.
        {apply /eqP.
        rewrite cards_eq0. apply /eqP. apply eq_finset.
        intro j. rewrite !in_set. destruct (j \in S1) eqn:E.
        + apply disjointFr with (x:=j) in H2.
          - by rewrite H2 /= andb_false_r.
          - by [].
        + by simpl.
        }
        by rewrite cardsU H11 subn0.
      * rewrite cardsT. assert(0 < F+1 /\ F+1 <= #|D|)%N.
        {by apply /andP. }
        by destruct H12.
    - rewrite cardsU H11 subn0 -ltnS addn1. by rewrite -> addn1 in H5.
  + split.
    - intros. exists 0%N. unfold malicious_at_i_t.
      assert(A i). {rewrite in_set in H11. by apply /eqP. }
      remember (incl_neigh_minus_extremes i (x mal init A (w_aux mal init A) 0)) as incl.
      rewrite /= H12 Heqmal. destruct (i \in S1) eqn:E0.
      * apply /eqP. apply Rlt_not_eq, non_neg_sum_with_pos_term_is_pos.
        -- intros. destruct (A (nth i incl n0)) eqn:E1.
           ** destruct (nth i incl n0 \in S1) eqn:E2.
              +++ nra.
              +++ apply Rmult_le_pos.
                  --- nra.
                  --- left. apply wts_gt_0 with (A:=A) (mal:=mal) (init:=init).
                      *** by rewrite -Heqmal.
                      *** rewrite Heqincl. apply mem_nth.
                          rewrite subn1 -ltnS in H13.
                          rewrite -Heqincl.
                          assert((size incl).-1.+1 = size incl)%N.
                          {apply prednK. rewrite Heqincl.
                          apply size_incl_not_0.
                          }
                          by rewrite -H14.
           ** rewrite Heqinit.
              destruct (nth i incl n0 \in S1) eqn:E2.
              +++ nra.
              +++ apply Rmult_le_pos.
                  --- destruct (nth i incl n0 \notin S2) eqn:E3.
                      *** nra.
                      *** nra.
                  --- left. apply wts_gt_0 with (A:=A) (mal:=mal) (init:=init).
                      *** by rewrite -Heqmal -Heqinit.
                      *** rewrite Heqincl. apply mem_nth.
                          rewrite subn1 -ltnS in H13.
                          rewrite -Heqincl.
                          assert((size incl).-1.+1 = size incl)%N.
                          {apply prednK. rewrite Heqincl.
                          apply size_incl_not_0.
                          }
                          by rewrite -H14.
        -- assert(exists (j:D), (j \in incl) /\ (j \notin S1)).
           {assert((R_i_greater_than mal init A (w_aux mal init A) i 0) \subset
           (in_neighbor i :\: S1) /\
           (exists2 x, x \in (in_neighbor i :\: S1) &
           x \notin (R_i_greater_than mal init A (w_aux mal init A) i 0))).
           {apply /properP. 
           assert(R_i_greater_than mal init A (w_aux mal init A) i 0 \subset
           in_neighbor i :\: S1).
           {apply /subsetP. intros j H14.
           assert(Hhelp: j != i).
           {destruct (j == i) eqn:E1.
           + assert(j = i). {by apply /eqP. }
             rewrite H13 in_set in H14.
             apply andb_triple_inject_left in H14.
             destruct Rgt_dec. nra. by [].
           + by [].
           }
           rewrite in_set in H14. rewrite in_set.
           apply /andP. split.
           + assert(0 = x mal init A (w_aux mal init A) 0 i)%Re.
             {unfold x. by rewrite H12 Heqmal E0. }
             apply andb_triple_inject_left in H14.
             rewrite -H13 in H14. destruct (A j) eqn:E1.
             - unfold x in H14. rewrite E1 Heqmal in H14.
               destruct (j \in S1) eqn:E2.
               * destruct Rgt_dec. nra. by [].
               * by [].
             - unfold x in H14.
               rewrite E1 Heqinit in H14. destruct (j \in S1) eqn:E2.
               * destruct Rgt_dec. nra. by [].
               * by [].
           + apply andb_triple_inject_right in H14.
             rewrite mem_sort mem_enum in_set in_set1 in H14.
             destruct (j == i). by []. by rewrite orb_false_r in H14.
           }
           rewrite properEcard H13 /=.
           assert((i \in S2) = false).
           {by apply disjointFr with (x:=i) in H2. }
           rewrite H7 !in_set E0 H14 /= orb_false_r in H11.
           assert(#|R_i_greater_than mal init A (w_aux mal init A) i 0| <= F)%N.
           {by apply R_i_gt_bounded. }
           apply leq_ltn_trans with
           (m:=#|R_i_greater_than mal init A (w_aux mal init A) i 0|)
           (n:=F) (p:=#|in_neighbor i :\: S1|).
           + by [].
           + apply ltn_leq_trans with
             (m:=F%N) (n:=(F+1)%N) (p:=#|in_neighbor i :\: S1|%N).
             - by rewrite addn1 ltnSn.
             - by [].
           }
           destruct H13.
           elim H14. intros j H15 H16. exists j. apply /andP.
           rewrite in_set in H15.
           assert(j \notin S1). {by destruct (j \notin S1). }
           rewrite H17 andb_true_r Heqincl incl_set_version mem_filter.
           assert(j \in in_neighbor i).
           {destruct (j \in in_neighbor i).
           by []. by rewrite andb_false_r in H15.
           }
           rewrite in_set mem_sort mem_enum in_set H18 /= andb_true_r in H16.
           rewrite mem_sort mem_enum in_setU H18 /= andb_true_r.
           rewrite andb_comm in_set H16 /= in_set.
           apply /nandP. left. unfold x. rewrite not_Rlt_Rge H12 Heqmal E0.
           assert(j \in S1 = false). {by destruct (j \in S1). }
           rewrite Heqinit H19. destruct (A j).
           + destruct Rge_dec. by []. nra.
           + destruct (j \notin S2).
             - destruct Rge_dec. by []. nra.
             - destruct Rge_dec. by []. nra.
           }
           elim H13. intros j H14. destruct H14.
           exists (index j incl). split.
           ** assert((size incl).-1.+1 = size incl)%N.
              {rewrite Heqincl. apply prednK, size_incl_not_0. }
              by rewrite subn1 -ltnS H16 index_mem.
           ** assert(aux: j \in incl). {by []. }
              apply nth_index with (x0:=i) in H14.
              rewrite H14. destruct (A j) eqn:E1.
              +++ destruct (j \in S1) eqn:E2.
                  --- by [].
                  --- apply Rmult_lt_0_compat.
                      *** nra.
                      *** apply wts_gt_0 with (A:=A) (mal:=mal) (init:=init).
                          ++++ by rewrite -Heqmal.
                          ++++ by rewrite -Heqincl.
              +++ rewrite Heqinit. destruct (j \in S1) eqn:E2.
                  --- by [].
                  --- destruct (j \notin S2) eqn:E3.
                      *** apply Rmult_lt_0_compat.
                          ++++ nra.
                          ++++ apply wts_gt_0 with (A:=A) (mal:=mal) (init:=init).
                               ---- by rewrite -Heqmal -Heqinit.
                               ---- by rewrite -Heqincl.
                      *** apply Rmult_lt_0_compat.
                          ++++ nra.
                          ++++ apply wts_gt_0 with (A:=A) (mal:=mal) (init:=init).
                               ---- by rewrite -Heqmal -Heqinit.
                               ---- by rewrite -Heqincl.
      * apply /eqP. apply Rgt_not_eq.
        assert((size incl).-1.+1 = size incl)%N.
        {rewrite Heqincl. apply prednK, size_incl_not_0. }
        rewrite -Heqmal.
        rewrite <- w_coeff_sum_to_1_implies_sum_eq_orig with
        (i:=i) (t:=0%N) (mal:=mal) (init:=init) (A:=A) (w:=(w_aux mal init A)) at 1.
        -- rewrite -Heqincl. apply Rle_neg_sum_with_Rlt_term_is_lt.
           ** intros. rewrite Rmult_comm. apply Rmult_le_compat_l.
              +++ left.
                  apply wts_gt_0 with (A:=A) (mal:=mal) (init:=init).
                  --- by [].
                  --- rewrite -Heqincl. apply mem_nth.
                      by rewrite subn1 -ltnS H13 in H14.
              +++ rewrite Heqinit. destruct (nth i incl n0 \in S1).
                  --- destruct (A (nth i incl n0)). nra. nra.
                  --- destruct (A (nth i incl n0)). nra.
                      destruct (nth i incl n0 \notin S2). nra. nra.
           ** exists 0%N. split.
              +++ rewrite subn1 -ltnS H13 Heqincl. apply size_incl_not_0.
              +++ assert(aux: A i). {by []. }
                  rewrite HeqA !in_set E0 /= in H12.
                  assert(F + 1 <= #|in_neighbor i :\: S2|)%N. {by destruct (i \in S2). }
                  assert((R_i_less_than mal init A (w_aux mal init A) i 0) \subset
                  (in_neighbor i :\: S2) /\
                  (exists2 x, x \in (in_neighbor i :\: S2) &
                  x \notin (R_i_less_than mal init A (w_aux mal init A) i 0))).
                  {apply /properP. 
                  assert(R_i_less_than mal init A (w_aux mal init A) i 0 \subset
                  in_neighbor i :\: S2).
                  {apply /subsetP. intros j H15.
                  assert(Hhelp: j != i).
                  {destruct (j == i) eqn:E1.
                  + assert(j = i). {by apply /eqP. }
                    rewrite H16 in_set in H15.
                    apply andb_triple_inject_left in H15.
                    destruct Rlt_dec. nra. by [].
                  + by [].
                  }
                  rewrite in_set in H15. rewrite in_set.
                  assert(1 = x mal init A (w_aux mal init A) 0 i)%Re.
                  {unfold x. by rewrite aux Heqmal E0. }
                  apply /andP. split.
                  + destruct (j \in S2) eqn:E2.
                    - assert(j \in S1 = false).
                      {by apply disjointFl with (x:=j) in H2. }
                      apply andb_triple_inject_left in H15.
                      rewrite -H16 in H15. unfold x in H15.
                      destruct (A j) eqn:E3.
                      * rewrite Heqmal H17 in H15.
                        destruct Rlt_dec. nra. by [].
                      * rewrite Heqinit H17 E2 /= in H15.
                        destruct Rlt_dec. nra. by [].
                    - by [].
                  + apply andb_triple_inject_right in H15.
                    assert((j == i) = false).
                    {by destruct (j == i). }
                    by rewrite mem_sort mem_enum in_set in_set1 H17 orb_false_r in H15.
                  }
                  rewrite properEcard H15 /=.
                  apply ltn_leq_trans with (n:=(F+1)%N).
                  + rewrite addn1 ltnS. apply R_i_lt_bounded.
                  + by destruct (i \in S2).
                  }
                  destruct H15. elim H16. intros j H17 H18.
                  assert(x mal init A (w_aux mal init A) 0 j < 1)%Re.
                  {unfold x. destruct (A j) eqn:E1.
                  + rewrite Heqmal.
                    assert(j \in S1 = true).
                    {rewrite in_set in H17.
                    assert(j \in S2 = false). {by destruct (j \in S2). }
                    rewrite HeqA !in_set H19 /= orb_false_r in E1.
                    by destruct (j \in S1).
                    }
                    rewrite H19. nra.
                  + rewrite Heqinit.
                    destruct (j \in S1) eqn:E2.
                    - nra.
                    - assert(j \in S2 = false).
                      {rewrite in_set in H17. by destruct(j \in S2). }
                      rewrite H19 /=. nra.
                  }
                  assert(x mal init A (w_aux mal init A) 0 i = 1)%Re.
                  {unfold x. by rewrite aux Heqmal E0. }
                  assert(j \notin R_i_greater_than_maybe_not_neighbors mal init A (w_aux mal init A) i 0).
                  {rewrite in_set nandb. apply /orP. left.
                  rewrite not_Rgt_Rle. destruct Rle_dec.
                  + by [].
                  + simpl. apply Rnot_le_lt in n.
                    rewrite H20 in n.
                    assert(x mal init A (w_aux mal init A) 0 j <
                    x mal init A (w_aux mal init A) 0 j)%Re.
                    {by apply Rlt_trans with (r2:=1). }
                    by apply Rlt_not_eq in H21.
                  }
                  assert(j \in inclusive_neighbor_list i (x mal init A (w_aux mal init A) 0)).
                  {rewrite mem_sort mem_enum in_set. rewrite in_set in H17.
                  destruct (j \in in_neighbor i) eqn:E. by simpl.
                  by rewrite andb_false_r in H17.
                  }
                  assert(j \in incl).
                  {rewrite Heqincl incl_set_version mem_filter.
                  assert(j \notin
                  R_i_less_than_maybe_not_neighbors mal init A (w_aux mal init A) i 0).
                  {rewrite in_set in H18. apply norb_triple in H18.
                  rewrite H22 orb_false_r in H18.
                  by rewrite in_set nandb.
                  }
                  by rewrite H21 H22 H23.
                  }
                  rewrite Heqincl in H23.
                  apply first_incl_is_min in H23.
                  rewrite -Heqincl in H23.
                  unfold x in H23 at 1.
                  rewrite Rmult_comm.
                  apply Rmult_gt_compat_l.
                  --- apply wts_gt_0 with (A:=A) (mal:=mal) (init:=init).
                      *** by [].
                      *** rewrite Heqincl. apply mem_nth, size_incl_not_0.
                  --- apply Rlt_gt.
                      rewrite -> Heqmal in H23. rewrite <- Heqmal in H23.
                      by apply Rle_lt_trans with (r2:= x mal init A (w_aux mal init A) 0 j).
        -- unfold wts_well_behaved in H6. elim H6. clear H6.
           intros a H6. destruct H6. destruct H14.
           specialize (H15 0%N i). destruct H15. by destruct H16.
    - intros. apply all_not_not_ex. intros t.
      unfold malicious_at_i_t.
      remember (incl_neigh_minus_extremes j (x mal init A (w_aux mal init A) t)) as incl.
      assert(A j = false).
      {rewrite !in_set andb_true_r in H11. by destruct (A j). }
      rewrite addn1. unfold x at 1. rewrite H12.
      assert(x = (fix x (mal : nat -> D -> R) (init : D -> R)
      (A : D -> bool) (w : nat -> D * D -> R) (t : nat) (i : D) {struct t} : R :=
      if A i then mal t i else match t with
      | 0%N => init i
      | t'.+1 => sum_f_R0 (fun n : nat => (x mal init A w t'
        (nth i (incl_neigh_minus_extremes i (x mal init A w t')) n) *
        w t' (i, nth i (incl_neigh_minus_extremes i
        (x mal init A w t')) n))%Re)
        (size (incl_neigh_minus_extremes i (x mal init A w t')) - 1)
      end)).
      {by []. }
      rewrite -H13 -Heqincl. unfold not. intro.
      assert(sum_f_R0 (fun n : nat => (x mal init A (w_aux mal init A) t (nth j incl n) *
      (w_aux mal init A) t (j, nth j incl n))%Re) (size incl - 1) <> sum_f_R0
      (fun n : nat => (x mal init A (w_aux mal init A) t (nth j incl n) *
      (w_aux mal init A) t (j, nth j incl n))%Re) (size incl - 1)).
      {by apply /eqP. }
      by [].
  }
  split.
  - by [].
  - apply <- not_implies_as_and. split. by [].
    apply nand_temp. left. apply all_not_not_ex. intro L.
    assert(S1 :&: Normal A != set0).
    {assert((Xi_S_r S1 (F + 1)) \subset S1 /\
    (exists2 x, x \in S1 & x \notin (Xi_S_r S1 (F + 1)))).
    {by apply /properP. }
    destruct H12. elim H13. intros k H14 H15. apply /set0Pn. exists k.
    rewrite in_setI. apply /andP. split.
    + by [].
    + rewrite in_setD !in_set andb_true_r HeqA.
      destruct (k \in Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1)) eqn:E.
      - rewrite in_setU in E.
        assert((k \in Xi_S_r S1 (F + 1)) \/ (k \in Xi_S_r S2 (F + 1))).
        {by apply /orP. }
        destruct H16.
        * by rewrite H16 in H15.
        * rewrite in_set in H16.
          assert(k \in S2). {by destruct (k \in S2). }
          apply disjointFr with (x:=k) in H2.
          ++ by rewrite H17 in H2.
          ++ by [].
      - by [].
    }
    assert(S2 :&: Normal A != set0).
    {assert(Xi_S_r S2 (F + 1) \proper S2).
    {rewrite properEcard.
    destruct (Xi_S_r S2 (F + 1) \subset S2) eqn:E.
    + simpl.
      destruct (Xi_S_r S2 (F + 1) == S2) eqn:E0.
      - assert(Xi_S_r S2 (F + 1) = S2). {by apply /eqP. }
        rewrite H13 in H4.
        assert(#|S2| <> #|S2|). {by apply /eqP. }
        by [].
      - assert(Xi_S_r S2 (F + 1) \proper S2).
        {by rewrite properEneq E E0. }
        by apply proper_card.
    + by [].
    }
    assert((Xi_S_r S2 (F + 1)) \subset S2 /\
    (exists2 x, x \in S2 & x \notin (Xi_S_r S2 (F + 1)))).
    {by apply /properP. }
    destruct H14. elim H15. intros k H16 H17.
    apply /set0Pn.
    exists k.
    rewrite in_setI. apply /andP. split.
    + by [].
    + rewrite in_setD !in_set andb_true_r HeqA.
      destruct (k \in Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1)) eqn:E.
      - rewrite in_setU in E.
        assert((k \in Xi_S_r S1 (F + 1)) \/ (k \in Xi_S_r S2 (F + 1))).
        {by apply /orP. }
        destruct H18.
        * rewrite in_set in H18.
          assert(k \in S1). {by destruct (k \in S1). }
          apply disjointFr with (x:=k) in H2.
          ** by rewrite H16 in H2.
          ++ by [].
        * by rewrite H18 in H17.
      - by [].
    }
    assert(exists (j1:D), j1 \in S1 /\ j1 \in Normal A).
    {assert(exists (j1:D), j1 \in S1 :&: Normal A).
    {by apply /set0Pn. }
    elim H14. intros j1 H15. exists j1. rewrite in_setI in H15.
    by apply /andP.
    }
    assert(exists (j2:D), j2 \in S2 /\ j2 \in Normal A).
    {assert(exists (j2:D), j2 \in S2 :&: Normal A).
    {by apply /set0Pn. }
    elim H15. intros j2 H16. exists j2. rewrite in_setI in H16.
    by apply /andP.
    }
    apply ex_not_not_all.
    assert(Rbar_eq_dec L 0%Re \/ ~ (Rbar_eq_dec L 0%Re)).
    {destruct Rbar_eq_dec. by left. by right. }
    destruct H16. destruct Rbar_eq_dec.
    * elim H15. clear H15. intros j2 H15. exists j2.
      apply not_implies_as_and. split.
      ++ by destruct H15.
      ++ rewrite e is_lim_seq_Reals. unfold Un_cv.
         apply ex_not_not_all. exists 1%Re.
         apply not_implies_as_and. split.
         -- nra.
         -- apply all_not_not_ex. intro N.
            apply ex_not_not_all. exists (N+1)%N.
            apply not_implies_as_and. split.
            ** apply /leP. by rewrite addn1 leqnSn.
            ** apply Rle_not_lt.
               assert(forall (j:D), j \in S2 :&: Normal A -> ~~ (A j)).
               {intros. rewrite HeqA inE. apply /norP.
               rewrite in_set in H17.
               assert(j \in S2 /\ j \in Normal A).
               {by apply /andP. }
               destruct H18. rewrite !in_set andb_comm /= HeqA in H19.
               destruct (j \in Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1)) eqn:E.
               + by [].
               + rewrite in_set in E. apply /norP. by rewrite E.
               }
               assert(forall (j:D),
               j \in S2 :&: Normal A -> A j = false).
               {intros. specialize (H17 j). apply H17 in H18.
               by destruct (A j).
               }
               assert((x mal init A (w_aux mal init A) (N + 1) j2) = 1)%Re.
               {assert(forall (t:nat) (j:D),
               j \in S2 -> (x mal init A (w_aux mal init A) t j = 1)%Re).
               {induction t as [|t' IHt'].
               + intros. unfold x.
                 assert(j \in S1 = false).
                 {by apply disjointFl with (x:=j) in H2. }
                 destruct (A j).
                 - by rewrite Heqmal H20.
                 - by rewrite Heqinit H20 H19 /=.
               + intros. simpl. destruct (A j) eqn:E.
                 - assert(j \in S1 = false).
                   {by apply disjointFl with (x:=j) in H2. }
                   by rewrite Heqmal H20.
                 - remember (incl_neigh_minus_extremes j (x mal init A (w_aux mal init A) t')) as incl.
                   elim H6. intros a H20. destruct H20. destruct H21.
                   specialize (H22 t' j).
                   assert(j \in Normal A).
                   {by rewrite !in_set E. }
                   destruct H22. destruct H24. rewrite -H25 -Heqincl.
                   apply (@Reals.PartSum.sum_eq (fun n : nat =>
                   (x mal init A (w_aux mal init A) t' (nth j incl n) *
                   (w_aux mal init A) t' (j, nth j incl n))%Re)
                   (fun n : nat => (w_aux mal init A) t' (j, nth j incl n))
                   (size incl - 1)).
                   intros n H26.
                   assert((w_aux mal init A) t' (j, nth j incl n) =
                   (1 * (w_aux mal init A) t' (j, nth j incl n)))%Re. {nra. }
                   rewrite -> H27 at 2. apply Rmult_eq_compat_r.
                   assert(nth j incl n \in incl).
                   {apply mem_nth.
                   assert((size incl).-1.+1 = size incl)%N.
                   {apply prednK. rewrite Heqincl.
                   apply size_incl_not_0.
                   }
                   rewrite -H28 ltnS -subn1. by apply /leP.
                   }
                   assert(j \notin Xi_S_r S1 (F + 1) :|: Xi_S_r S2 (F + 1)).
                   {rewrite HeqA in E. by rewrite E. }
                   assert(j \notin S1).
                   {assert(j \in S1 = false).
                   {by apply disjointFl with (x:=j) in H2. }
                   by rewrite H30.
                   }
                   rewrite in_set norb !in_set !nandb H19 H30 /= -ltnNge in H29.
                   assert(R_i_less_than mal init A (w_aux mal init A) j t' \subset in_neighbor j :\: S2).
                   {apply /subsetP. intros k H31.
                   rewrite in_set. rewrite in_set in H31.
                   destruct (k == j) eqn:E0.
                   + assert(k = j). {by apply /eqP. }
                     apply andb_triple_inject_left in H31.
                     rewrite H32 in H31. destruct Rlt_dec. simpl in H31.
                     by apply Rlt_irrefl in r. by [].
                   + assert(k \in in_neighbor j).
                     {apply andb_triple_inject_right in H31.
                     by rewrite mem_sort mem_enum in_set in_set1 E0 orb_false_r in H31.
                     }
                     rewrite H32 andb_true_r.
                     assert((x mal init A (w_aux mal init A) t' k) <
                     (x mal init A (w_aux mal init A) t' j))%Re.
                     {by destruct Rlt_dec. }
                     destruct (k \in S2) eqn:E1.
                     - apply IHt' in E1. apply IHt' in H19.
                       rewrite E1 H19 in H33. nra.
                     - by [].
                   }
                   destruct (in_neighbor j :\: S2 \subset
                   R_i_less_than mal init A (w_aux mal init A) j t') eqn:E0.
                   * assert(in_neighbor j :\: S2 =
                     R_i_less_than mal init A (w_aux mal init A) j t').
                     {apply /eqP. by rewrite eqEsubset H31 E0. }
                     assert(nth j incl n \notin
                     R_i_less_than mal init A (w_aux mal init A) j t').
                     {apply R_i_lt_and_incl_disjoint.
                     rewrite -Heqincl. apply mem_nth.
                     assert((size incl).-1.+1 = size incl).
                     {apply prednK. rewrite Heqincl.
                     apply size_incl_not_0.
                     }
                     rewrite -H33 ltnS -subn1. by apply /leP.
                     }
                     rewrite -H32 in_set nandb in H33.
                     destruct ((nth j incl n) == j) eqn:E1.
                     ++ assert(nth j incl n = j).
                        {by apply /eqP. }
                        rewrite H34. by apply IHt'.
                     ++ assert(nth j incl n \in in_neighbor j).
                        {assert(nth j incl n \in incl).
                        {apply mem_nth.
                        assert((size incl).-1.+1 = size incl).
                        {apply prednK. rewrite Heqincl.
                        apply size_incl_not_0.
                        }
                        rewrite -H34 ltnS -subn1. by apply /leP.
                        }
                        rewrite Heqincl mem_filter -Heqincl in H34.
                        apply andb_triple_inject_right in H34.
                        by rewrite mem_sort mem_enum in_set in_set1 E1 orb_false_r in H34.
                        }
                        rewrite H34 orb_false_r in H33.
                        apply IHt'. by destruct (nth j incl n \in S2).
                   * assert(R_i_less_than mal init A (w_aux mal init A) j t' \proper
                     in_neighbor j :\: S2).
                     {by rewrite properE H31 E0. }
                     apply proper_card in H32.
                     assert(#|R_i_less_than mal init A (w_aux mal init A) j t'| < F)%N.
                     {rewrite addn1 in H29.
                     by apply ltn_leq_trans with (n:=#|in_neighbor j :\: S2|).
                     }
                     apply card_R_i_lt_lt_F_exchange_first in H33.
                     apply IHt' in H19. rewrite H19 -Heqincl in H33.
                     apply Rle_antisym.
                     ++ destruct (A (nth j incl n)) eqn:H34.
                        -- destruct t' as [|t''].
                           ** unfold x. rewrite H34 Heqmal.
                              destruct (nth j incl n \in S1). nra. nra.
                           ** unfold x. rewrite H34 Heqmal.
                              destruct (nth j incl n \in S1). nra. nra.
                        -- assert(M mal init A (w_aux mal init A) 0 = 1)%Re.
                           {assert(forall (k:D), k \in S2 -> x mal init A (w_aux mal init A) 0 k = 1)%Re.
                           {intros. unfold x. rewrite Heqmal Heqinit.
                           assert(k \in S1 = false). {by apply disjointFl with (x:=k) in H2. }
                           destruct (A k).
                           + by rewrite H36.
                           + by rewrite H36 H35 /=.
                           }
                           destruct H15. apply H35 in H15. rewrite -H15.
                           apply /bigmaxrP. split.
                           + apply /map_f. by rewrite mem_enum.
                           + intros q H37. assert(forall (k:D), x mal init A (w_aux mal init A) 0 k <=1)%Re.
                             {intro. unfold x. rewrite Heqmal Heqinit.
                             destruct (A k).
                             + destruct (k \in S1). nra. nra.
                             + destruct (k \in S1). nra. destruct (k \notin S2). nra. nra.
                             } remember [seq x mal init A (w_aux mal init A) 0 i | i <- enum (Normal A)] as x_incl.
                             rewrite Heqx_incl. rewrite H15. 
                             assert(nth 0%Re ((map (fun i:D => x mal init A (w_aux mal init A) 0 i)) (enum (Normal A))) q 
                             = (fun i:D => x mal init A (w_aux mal init A) 0 i) (nth key (enum (Normal A)) q)).
                             {apply (@nth_map D key R 0%Re (fun i:D => x mal init A (w_aux mal init A) 0 i) q). 
                             rewrite Heqx_incl in H37. by rewrite size_map in H37.
                             }
                             rewrite H39. apply /RleP. apply H38.
                           }
                           assert((nth j incl n) \in Normal A).
                           {by rewrite !in_set H34. }
                           assert((m mal init A (w_aux mal init A) 0 <= m mal init A (w_aux mal init A) t')%Re /\
                           (M mal init A (w_aux mal init A) t' <= M mal init A (w_aux mal init A) 0)%Re).
                           {by apply interval_bound. }
                           assert(((x mal init A (w_aux mal init A) (t'.-1 + 1) (nth j incl n) <= M mal init A (w_aux mal init A) t'.-1)%Re /\
                           (m mal init A (w_aux mal init A) t'.-1 <= x mal init A (w_aux mal init A) (t'.-1 + 1) (nth j incl n))%Re)).
                           {assert (forall (i:D) (t:nat) (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (w:nat -> D*D -> R),
                           F_total_malicious mal init A w ->
                           wts_well_behaved A mal init w ->
                           i \in Normal A ->
                           ((x mal init A w (t+1) i <= M mal init A w t)%Re /\
                           (m mal init A w t <= x mal init A w (t+1) i)%Re)).
                           {by apply lem_1. }
                           by apply H38.
                           } simpl in H16.
                           rewrite -H35. apply Rle_trans with (M mal init A (w_aux mal init A) t').
                           + by apply x_bound.
                           + by destruct H37.
                     ++ rewrite -H33 Heqincl.
                        apply first_incl_is_min. by rewrite -Heqincl. by [].
               }
               apply H19. by destruct H15.
               }
               assert(1 - 0 = 1)%Re. {nra. }
               unfold R_dist. rewrite H19 H20 Rabs_R1. by right. by [].
    * destruct Rbar_eq_dec. by []. elim H14. clear H14. intros j1 H14. exists j1.
      apply not_implies_as_and. split.
      ++ by destruct H14.
      ++ rewrite lim_is_0_or_1.
         -- by []. 
         -- split.
            ** by [].
            ** split.
               +++ by [].
               +++ split.
                   --- by [].
                   --- exists S1. exists S2. destruct H0. destruct H1.
                       destruct H14. rewrite Heqmal -Heqinit.
                       repeat split; try by [].
Qed.