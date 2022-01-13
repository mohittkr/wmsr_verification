Require Import Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra finset.
From GraphTheory Require Import digraph.
From Coquelicot Require Import Lim_seq Rbar.
From mathcomp.analysis Require Import Rstruct.
From Coq Require Import Logic.Classical_Pred_Type.
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

Notation D:= definitions.D.
Notation F:= definitions.F.


Axiom P_not_not_P: forall (P:Prop), P <->  ~(~ P).


Lemma const_ineq_exists: forall (A_M A_m:R),
  (A_M > A_m)%Re -> 
  (exists eps_0: posreal, (A_m + eps_0 < A_M - eps_0)%Re).
Proof.
intros.
assert ((0< (A_M - A_m)/3)%Re).
{ apply Rmult_lt_0_compat.
  + nra. 
  + apply Rinv_0_lt_compat. nra.
}
exists (mkposreal ((A_M - A_m)/3)%Re H0).
simpl.
assert( (A_m + (A_M - A_m) / 3)%Re = ((A_M + 2* A_m)/3)%Re).
{ nra. } rewrite H1.
assert ((A_M - (A_M - A_m) / 3)%Re = ((2*A_M + A_m)/3)%Re).
{ nra. } rewrite H2.
apply  Rmult_lt_compat_r .
+ apply Rinv_0_lt_compat. nra.
+ nra.
Qed.

Variable key:D.


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


Lemma add_max_bound: forall (B C F:nat),
  (F+1 <= B+C)%N -> (C <= F)%N -> (1 <= B)%N.
Proof.
intros. 
assert ( 1%N = ((F+1) - F)%N). 
{ rewrite addn1. by rewrite subSnn. }
rewrite H1.
assert (B = ((B+C) - (0 + C))%N).
{ assert (B = (B-0)%N). { by rewrite subn0. }
  rewrite [in LHS]H2. by rewrite subnDr.
} rewrite H2. rewrite add0n.
by apply leq_sub.
Qed.

Lemma normal_or_adversary: forall (i:D) (A: D -> bool), 
  ( i \in Normal_general A) \/ (i \in Adversary_general A).
Proof.
intros. apply /orP. rewrite -in_setU.
assert (Adversary_general A = ~: Normal_general A).
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
  Normal_general A = ~:Adversary_general A.
Proof.
apply eq_finset. unfold eqfun. intros. 
destruct ((x \notin Adversary_general A)).
+ by rewrite in_setT.
+ by [].
Qed.


Lemma cardD_sum (A: D -> bool): 
  #|D| =( #|Normal_general A| + #|Adversary_general A|)%N.
Proof.
rewrite -cardsUI.
assert (#|Normal_general A :&: Adversary_general A| = 0%N).
{ apply /eqP. rewrite cards_eq0. apply /eqP.
  apply eq_finset. unfold eqfun. move =>k.
  apply a_and_b_false_implies.
  intros. rewrite -in_setC. by rewrite -Normal_not_adversary.
} rewrite H addn0. rewrite Normal_not_adversary.
rewrite setUC setUCr. by rewrite cardsT.
Qed.


Lemma size_normal_gt_0 (A: D -> bool): 
  F_totally_bounded_general A ->
  (0 < F + 1 <= #|D|)%N -> 
  (0 < size (enum (Normal_general A)))%N.
Proof.
intros. 
assert ((0 < F+1)%N /\ (F+1 <= #|D|)%N).
{ by apply /andP. } destruct H1. rewrite -cardE.
rewrite (cardD_sum  A) in H2. 
apply (@add_max_bound #|Normal_general A| #|Adversary_general A| F) in H2.
+ by [].
+ rewrite /F_totally_bounded_general /F_total in H. by destruct H.
Qed.


Lemma in_enum_Normal: forall (i:D) (l:{set D}),
  i \in enum l -> i \in l.
Proof.
intros.  
assert ([set x | x \in enum l] = l).
{ apply set_enum. } rewrite -H0.
by rewrite inE.
Qed.


Lemma normal_set_to_enum: forall (i:D) (A: D -> bool),
  i \in Normal_general A -> i \in enum (Normal_general A).
Proof.
intros.
assert ([set x | x \in enum (Normal_general A)] = Normal_general A).
{ apply set_enum. } rewrite -H0 in H.
by rewrite inE in H.
Qed.


Lemma nth_normal: forall (i:nat)(A: D -> bool), 
  (i < size (enum (Normal_general A)))%N ->  
  nth key (enum (Normal_general A)) i \in (Normal_general A).
Proof.
intros.
assert ( nth key (enum (Normal_general A)) i \in enum (Normal_general A) ->
          nth key (enum (Normal_general A)) i \in (Normal_general A)).
{ apply (@in_enum_Normal (nth key (enum (Normal_general A)) i) (Normal_general A)). }
by apply H0, mem_nth.
Qed.


Lemma x_bound: forall (i:D) (A: D -> bool) (mal : nat -> D -> R) (init: D -> R), 
  i \in (Normal_general A) ->  
  forall t : nat, (m_general mal init A t <= x_general mal init A t i <= M_general mal init A t)%Re.
Proof.
intros. 
(** x_general mal init A t i <= Rmax (x_general mal init A t i) (M - (x_general mal init A t i))
    Rmin (x_general mal init A t i) (m - (x_general mal init A t i)) <= x_general mal init A t i
**)
split.
+ assert (m_general mal init A t = -(bigmaxr 0 ((map (fun i:D => -(x_general mal init A t i))) (enum (Normal_general A))))).
  { by rewrite /m_general. } rewrite H0.
  assert ( x_general mal init A t i = (- (- (x_general mal init A t i)))). 
  { rewrite -!RoppE. by rewrite Ropp_involutive. } rewrite H1.
  apply Ropp_le_contravar. rewrite -RoppE.
  assert ( nth 0%Re ((map (fun i:D => -(x_general mal init A t i))) (enum (Normal_general A))) 
            (index i (enum (Normal_general A)))= 
                     (fun i:D => - (x_general mal init A t i)) (nth key (enum (Normal_general A)) 
            (index i (enum (Normal_general A))))).
  { apply (@nth_map D key R 0%Re (fun i:D => -(x_general mal init A t i)) (index i (enum (Normal_general A))) (enum (Normal_general A))).
    rewrite index_mem. by apply normal_set_to_enum.
  }
  assert ((- x_general mal init A t i)%Re  = (fun i : D => - x_general mal init A t i) (nth key (enum (Normal_general A))
          (index i (enum (Normal_general A))))).
  { assert ( i  = nth key (enum (Normal_general A)) (index i (enum (Normal_general A)))).
    { symmetry. by apply nth_index, normal_set_to_enum. }
    by rewrite [in LHS]H3.
  } rewrite H3. rewrite -H2.
  apply /RleP. 
  apply (@bigmaxr_ler _ 0%Re [seq - x_general mal init A t i0 | i0 <- enum (Normal_general A)] (index i (enum (Normal_general A))) ). 
  rewrite size_map. rewrite index_mem. by apply normal_set_to_enum.
+ assert (M_general mal init A t = bigmaxr 0 (map (x_general mal init A t) (enum (Normal_general A)))).
  { by rewrite /M_general. } rewrite H0. apply normal_set_to_enum in H.
  clear H0.
  assert ( nth 0%Re ((map (fun i:D => (x_general mal init A t i))) (enum (Normal_general A))) 
            (index i (enum (Normal_general A)))= 
                     (fun i:D => (x_general mal init A t i)) (nth key (enum (Normal_general A)) 
            (index i (enum (Normal_general A))))).
  { apply (@nth_map D key R 0%Re (fun i:D => (x_general mal init A t i)) (index i (enum (Normal_general A))) (enum (Normal_general A))).
    by rewrite index_mem. 
  }
  assert ((x_general mal init A t i)%Re  = (fun i : D => x_general mal init A t i) (nth key (enum (Normal_general A))
          (index i (enum (Normal_general A))))).
  { assert ( i  = nth key (enum (Normal_general A)) (index i (enum (Normal_general A)))).
    { symmetry. by apply nth_index. }
    by rewrite [in LHS]H1.
  } rewrite H1. rewrite -H0.
  apply /RleP.
  apply (@bigmaxr_ler _ 0%Re [seq x_general mal init A t i0 | i0 <- enum (Normal_general A)] (index i (enum (Normal_general A))) ). 
  by rewrite size_map index_mem.
Qed.

Lemma order_m (A: D -> bool) (mal : nat -> D -> R) (init : D -> R): 
  F_totally_bounded_general A ->
  (0 < F + 1 <= #|D|)%N -> 
  forall t : nat, (m_general mal init A t <= M_general mal init A t)%Re.
Proof.
intros. rewrite /m_general  /M_general.
apply Rle_trans with 
  (-(nth 0%Re [seq (- x_general mal init A  t i)%Ri | i <- enum (Normal_general A)] (size (enum (Normal_general A))).-1))%Re.
+ apply Ropp_le_contravar. apply /RleP.
  apply (@bigmaxr_ler _ 0%Re [seq - x_general mal init A t i0 | i0 <- enum (Normal_general A)] (size (enum (Normal_general A))).-1).
  rewrite size_map. rewrite ltn_predL. by apply size_normal_gt_0.
+ assert ((- nth 0 [seq (- x_general mal init A t i)%Ri | i <- enum (Normal_general A)]
              (size (enum (Normal_general A))).-1)%Re = 
          nth 0 [seq x_general mal init A t i | i <- enum (Normal_general A)]
              (size (enum (Normal_general A))).-1).
  { rewrite -(@nth_map R 0%Re R 0%Re (fun x:R => (- x)%Re) 
          (size (enum (Normal_general A))).-1 [seq (- x_general mal init A t i)%Ri | i <- enum (Normal_general A)]).
    + assert ([seq (- x)%Re | x <- [seq - x_general mal init A t i | i <- enum (Normal_general A)]] = 
                [seq x_general mal init A t i | i <- enum (Normal_general A)]).
      { rewrite -map_comp.
        apply eq_in_map. 
        rewrite /eqfun //=. 
        assert ( (forall i:D, i \in (enum (Normal_general A)) -> 
                  (- ( - (x_general mal init A t i))%Ri)%Re = x_general mal init A t i) <-> 
                  {in enum (Normal_general A),
                    forall x : D,
                    (- (-x_general mal init A t x)%Ri)%Re = x_general mal init A t x}).
        { by []. } rewrite -H1. intros.
        rewrite -RoppE. by rewrite Ropp_involutive.
      } by rewrite H1.
    + rewrite size_map ltn_predL. by apply size_normal_gt_0.
  } rewrite H1. apply /RleP.
  apply (@bigmaxr_ler _ 0%Re [seq x_general mal init A t i0 | i0 <- enum (Normal_general A)] (size (enum (Normal_general A))).-1 ). 
  rewrite size_map ltn_predL. by apply size_normal_gt_0. 
Qed.


Lemma interval_bound (A: D -> bool) (mal : nat -> D -> R) (init :D -> R):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N -> 
  forall t : nat,
  (m_general mal init A 0 <= m_general mal init A t)%Re /\ (M_general mal init A t <= M_general mal init A 0)%Re.
Proof.
intros. induction t.
  - nra.
  - destruct IHt as [mIHt MIHt].
    split.
    * apply Rle_trans with (m_general mal init A t)%Re.
      ++ apply mIHt.
      ++ assert (m_general mal init A t.+1 = -(bigmaxr 0 ((map (fun i:D => -(x_general mal init A t.+1 i))) (enum (Normal_general A))))).
         { by rewrite /m_general. } rewrite H2. clear H2.
         assert ( m_general mal init A t = (-(-(m_general mal init A t)))%Re). { by rewrite Ropp_involutive. }
         rewrite H2. apply Ropp_ge_le_contravar.
         apply Rle_ge. apply bigmax_le.
         - rewrite size_map. destruct H. by apply size_normal_gt_0.
         - intros. rewrite size_map in H3.
           assert ( nth 0%Re ((map (fun i:D => -(x_general mal init A t.+1 i))) (enum (Normal_general A))) i= 
                      (fun i:D => - (x_general mal init A t.+1 i)) (nth key (enum (Normal_general A)) i)).
           { by apply (@nth_map D key R 0%Re (fun i:D => -(x_general mal init A t.+1 i)) i (enum (Normal_general A))). }
           rewrite H4. apply Ropp_ge_le_contravar. apply Rle_ge.
           assert (forall (i:D) (t:nat) (mal : nat -> D -> R) (init: D ->R) (A: D -> bool),
                    F_total_malicious_general mal init A ->
                    wts_well_behaved_general A mal init ->
                    i \in Normal_general A ->
                    ((x_general mal init A (t+1) i <= M_general mal init A t)%Re /\ (m_general mal init A t <= x_general mal init A (t+1) i)%Re)).
           { apply lem_1_general. }
           specialize (H5 (nth key (enum (Normal_general A)) i)).
           specialize (H5 t mal init A H H0).
           assert (nth key (enum (Normal_general A)) i \in (Normal_general A)). 
           { apply nth_normal, H3. }
           specialize (H5 H6). rewrite -addn1. destruct H5.
           apply H7.
    * apply Rle_trans with (M_general mal init A t)%Re.
      ++ assert (M_general mal init A t.+1 = bigmaxr 0 (map (x_general mal init A t.+1) (enum (Normal_general A)))).
         { by rewrite /M_general. } rewrite H2. clear H2.
         apply bigmax_le.
         - rewrite size_map. destruct H. by apply size_normal_gt_0.
         - intros. rewrite size_map in H2.
           assert ( [seq x_general mal init A t.+1 i | i <- enum (Normal_general A)]`_i = 
                      (fun i:D => (x_general mal init A t.+1 i)) (nth key (enum (Normal_general A)) i)).
           { by apply nth_map. } rewrite H3.
           assert (forall (i:D) (t:nat) (mal : nat -> D ->R) (init: D -> R) (A: D -> bool),
                    F_total_malicious_general mal init A ->
                    wts_well_behaved_general A mal init ->
                    i \in Normal_general A ->
                    ((x_general mal init A (t+1) i <= M_general mal init A t)%Re /\ 
                      (m_general mal init A t <= x_general mal init A (t+1) i)%Re)).
           { apply lem_1_general. }
           specialize (H4 (nth key (enum (Normal_general A)) i)).
           specialize (H4 t mal init A H H0).
           assert (nth key (enum (Normal_general A)) i \in (Normal_general A)). 
           { apply nth_normal, H2. }
           specialize (H4 H5). rewrite -addn1. destruct H4.
           apply H4.
      ++ apply MIHt.
Qed.

(*** Lemma that for a bounded monotonous function
  there exists a limit ****)


Lemma A_M_exists (A: D -> bool) (mal : nat -> D -> R) (init: D -> R):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  (forall t:nat, (M_general mal init A t.+1 <= M_general mal init A t)%Re) -> 
  exists A_M: R, is_lim_seq (M_general mal init A) A_M.
Proof.
intros. 
assert (forall (u:nat -> R) (G:R),
          (forall t:nat, (u t.+1 <= u t)%Re) ->
          (forall t:nat, (G <= u t)%Re) -> 
          ex_finite_lim_seq u).
{ apply ex_finite_lim_seq_decr. }
rewrite /ex_finite_lim_seq in H3.
apply H3 with (m_general mal init A 0%N).
+ apply H2.
+ intros. apply Rle_trans with (m_general mal init A t).
  - by apply interval_bound.
  - destruct H. by apply order_m.
Qed.


Lemma A_m_exists (A: D -> bool) (mal : nat -> D -> R) (init: D -> R):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  (forall t:nat, (m_general mal init A t.+1 >= m_general mal init A t)%Re) -> 
  exists A_m: R,  is_lim_seq (m_general mal init A) A_m.
Proof.
intros.
assert (forall (u:nat -> R) (G:R),
          (forall t:nat, (u t <= u t.+1)%Re) ->
          (forall t:nat, (u t <= G)%Re) -> 
          ex_finite_lim_seq u).
{ apply ex_finite_lim_seq_incr. }
rewrite /ex_finite_lim_seq in H3.
apply H3 with (M_general mal init A 0%N).
+ intros. by apply Rge_le.
+ intros. apply Rle_trans with (M_general mal init A t).
  - destruct H. by apply order_m.
  - destruct H. by apply interval_bound.
Qed.


(** set of all normal and malicious nodes 
  that have values larger than A_M - e_i 
**)
Definition X_M_t_e_i (e_i: R) (A_M:R) (t:nat) (mal : nat -> D ->R)
  (init : D -> R) (A: D -> bool) :=
  [set i:D | Rgt_dec (x_general mal init A t i) (A_M - e_i)%Re].

(** Set of all normal and malicious nodes 
  that have values smaller than A_m + e_i 
**)
Definition X_m_t_e_i (e_i: R) (A_m :R) (t:nat) (mal : nat -> D -> R)
  (init : D -> R) (A: D -> bool) :=
  [set i:D | Rlt_dec (x_general mal init A t i) (A_m + e_i)%Re].


Lemma X_M_X_m_disjoint (mal : nat -> D ->R) (init : D -> R) (A: D -> bool) :
  forall (t:nat) (A_M A_m :R) (eps_0:posreal),
  (A_M - eps_0 > A_m + eps_0)%Re ->
  [disjoint (X_M_t_e_i eps_0 A_M t mal init A) & (X_m_t_e_i eps_0 A_m t mal init A)].
Proof.
intros. rewrite -setI_eq0. apply /eqP.
apply eq_finset. unfold eqfun. move=>i.
rewrite /X_M_t_e_i /X_m_t_e_i.
rewrite !in_set. apply /andP. 
apply /andP. apply /nandP.
destruct (Rgt_dec (x_general mal init A t i) (A_M - eps_0)).
+ simpl. 
  destruct (Rlt_dec (x_general mal init A t i) (A_m + eps_0)).
  - simpl. left.
    assert ((x_general mal init A t i > A_m + eps_0)%Re).
    { apply Rgt_trans with (A_M - eps_0)%Re; by []. }
    assert ((x_general mal init A t i > A_m + eps_0)%Re -> 
            ~(x_general mal init A t i < A_m + eps_0)%Re). { nra. }
    specialize (H1 H0).
    contradiction.
  - simpl. by right.
+ simpl. by left.
Qed.


Lemma card_size_rel: forall A: {set D},
  (0 < #|A|)%N -> (0 < size (enum A))%N.
Proof.
intros. by rewrite -cardE.
Qed.

Lemma single_element_disjoint: forall (A B: {set D}),
  (0 < #|A|)%N ->
  [disjoint A & B] -> [disjoint [set nth key (enum A) 0%N] & B].
Proof.
intros. rewrite disjoints1.
assert ( [disjoint A & B] -> nth key (enum A) 0 \in A -> 
          nth key (enum A) 0 \notin B).
{ intros.
  assert (  nth key (enum A) 0 \in B = false ->
             nth key (enum A) 0 \notin B).
  { intros. by apply ssrbool.negbT. }
  apply H3. move: H1 H2. apply disjointFr.
} apply H1.
+ apply H0.
+ by apply in_enum_Normal, mem_nth, card_size_rel.
Qed.

Lemma disjoint_sym: forall (A B: {set D}),
  [disjoint A & B] = [disjoint B & A].
Proof.
intros. rewrite -[in LHS]setI_eq0.
rewrite setIC. by rewrite [in LHS]setI_eq0.
Qed.

Lemma each_elem_disjoint (mal : nat ->D->R) (init : D -> R) (A: D -> bool):
  forall (t:nat) (A_M A_m :R) (eps_0:posreal),
  (A_M - eps_0 > A_m + eps_0)%Re -> 
  (0 < #|X_m_t_e_i eps_0 A_m t mal init A|)%N ->
  [disjoint
   [set nth key (enum (X_m_t_e_i eps_0 A_m t mal init A)) 0]
    & X_M_t_e_i eps_0 A_M t mal init A].
Proof.
intros. apply single_element_disjoint. apply H0.
rewrite disjoint_sym. by apply X_M_X_m_disjoint.
Qed.


Lemma X_M_mem (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  forall (t_eps:nat) (A_M A_m :R) (eps_0:posreal),
  (0 < #|D|)%N ->  (A_M - eps_0 > A_m + eps_0)%Re -> 
  (0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N -> 
  X_M_t_e_i eps_0 A_M t_eps mal init A \proper Vertex.
Proof.
intros.
rewrite properEcard.
apply /andP. split.
- apply subsetT.
- rewrite cardsCs.
  assert (#|[set: D]| = #|D|).
  { by rewrite cardsT. } rewrite H2.
  rewrite ltn_subrL. apply /andP. split.
  * rewrite card_gt0. apply /set0Pn.
    exists (nth key (enum (X_m_t_e_i eps_0 A_m t_eps mal init A)) 0%N).
    rewrite inE -disjoints1.
    apply single_element_disjoint.
    ++ by [].
    ++ rewrite disjoint_sym.
       by apply X_M_X_m_disjoint.
  * apply H.
Qed.


Lemma X_m_mem (mal : nat -> D ->R) (init : D ->R) (A: D -> bool):
  forall (t_eps:nat) (A_M A_m :R) (eps_0:posreal),
  (0 < #|D|)%N ->  (A_M - eps_0 > A_m + eps_0)%Re -> 
  (0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N -> 
  X_m_t_e_i eps_0 A_m t_eps mal init A \proper Vertex.
Proof.
intros.
rewrite properEcard.
apply /andP. split.
- apply subsetT.
- rewrite cardsCs.
  assert (#|[set: D]| = #|D|).
  { by rewrite cardsT. } rewrite H2.
  rewrite ltn_subrL. apply /andP. split.
  * rewrite card_gt0. apply /set0Pn.
    exists (nth key (enum (X_M_t_e_i eps_0 A_M t_eps mal init A)) 0%N).
    rewrite inE -disjoints1.
    apply single_element_disjoint.
    ++ by [].
    ++ by apply (@X_M_X_m_disjoint mal init A t_eps A_M A_m eps_0).
  * apply H.
Qed.


Lemma A_M_monotonic (mal: nat -> D ->R) (init : D-> R) (A: D -> bool): 
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
 (0 < F + 1 <= #|D|)%N ->
  forall t : nat, (M_general mal init A t.+1 <= M_general mal init A t)%Re.
Proof.
intros.
assert (M_general mal init A t.+1 = bigmaxr 0 (map (x_general mal init A t.+1) (enum (Normal_general A)))).
{ by rewrite /M_general. } rewrite H2.
apply bigmax_le.
+ rewrite size_map. destruct H. by apply size_normal_gt_0.
+ intros.
  assert ( nth 0%Re ((map (fun i:D => (x_general mal init A t.+1 i))) (enum (Normal_general A))) i= 
               (fun i:D => (x_general mal init A t.+1 i)) (nth key (enum (Normal_general A)) i)).
  { apply (@nth_map D key R 0%Re (fun i:D => (x_general mal init A t.+1 i)) i (enum (Normal_general A))). 
    rewrite size_map in H3. apply H3.
  } rewrite H4.
  assert (forall (i:D) (t:nat)  (mal : nat -> D ->R) (init: D -> R) (A: D -> bool),
                   F_total_malicious_general mal init A ->
                    wts_well_behaved_general A mal init ->
                    i \in Normal_general A ->
                    ((x_general mal init A (t+1) i <= M_general mal init A t)%Re /\ 
                  (m_general mal init A t <= x_general mal init A (t+1) i)%Re)).
  { apply lem_1_general. }
  specialize (H5 (nth key (enum (Normal_general A)) i)).
  specialize (H5 t mal init A H H0).
  assert (nth key (enum (Normal_general A)) i \in (Normal_general A)). 
  { apply nth_normal. rewrite size_map in H3. apply H3. }
  specialize (H5 H6). rewrite -addn1. destruct H5.
  apply H5.
Qed.

Lemma A_m_monotonic (A: D -> bool) (mal : nat -> D -> R) (init: D -> R):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  forall t:nat, (m_general mal init A t.+1 >= m_general mal init A t)%Re.
Proof.
intros. apply Rle_ge.
assert (m_general mal init A t.+1 = -(bigmaxr 0 ((map (fun i:D => -(x_general mal init A t.+1 i))) (enum (Normal_general A))))).
{ by rewrite /m_general. }
rewrite H2.
assert ( m_general mal init A t = (- (- (m_general mal init A t)))%Re).
{ by rewrite Ropp_involutive. } rewrite H3.
apply Ropp_le_contravar. apply bigmax_le.
+ rewrite size_map. destruct H. by apply size_normal_gt_0.
+ intros.
  assert ( nth 0%Re ((map (fun i:D => -(x_general mal init A t.+1 i))) (enum (Normal_general A))) i= 
               (fun i:D => - (x_general mal init A t.+1 i)) (nth key (enum (Normal_general A)) i)).
  { apply (@nth_map D key R 0%Re (fun i:D => -(x_general mal init A t.+1 i)) i (enum (Normal_general A))). 
    rewrite size_map in H4. apply H4.
  } rewrite H5. apply Ropp_le_contravar.
  assert (forall (i:D) (t:nat) (mal : nat ->D -> R) (init : D -> R) (A: D -> bool), 
              F_total_malicious_general mal init A->
               wts_well_behaved_general A mal init ->
              i \in (Normal_general A) ->
               ((x_general mal init A (t+1) i <= M_general mal init A t)%Re /\
               (m_general mal init A t <= x_general mal init A (t+1) i)%Re)).
  { apply lem_1_general. }
  specialize (H6 (nth key (enum (Normal_general A)) i)).
  specialize (H6 t mal init A H H0).
  assert (nth key (enum (Normal_general A)) i \in (Normal_general A)). 
  { apply nth_normal. rewrite size_map in H4. apply H4. }
  specialize (H6 H7). rewrite -addn1. destruct H6.
  apply H8.
Qed.

Theorem sandwich_func (mal :nat ->D ->R) (init: D ->R) (A: D -> bool):
 forall (u v : nat -> R),
(exists L:Rbar,  
   forall (i:D), i \in (Normal_general A) ->
   (forall t:nat, ((u t) <= (x_general mal init A t i) <= (v t))%Re) /\ 
   (is_lim_seq (fun t: nat => u t) L /\
    is_lim_seq (fun t: nat => v t) L) ) -> 
exists L : Rbar,
  forall i : D, i \in (Normal_general A) -> 
  is_lim_seq (fun t: nat => x_general mal init A t i) L.
Proof.
intros. destruct H as [L H].
exists L. intros. specialize (H i H0).
apply (is_lim_seq_le_le 
        (fun t: nat => u t) (fun t: nat => x_general mal init A t i)
        (fun t: nat => v t)).
+ destruct H as [H H1].
  destruct H1 as [H1 H2]. apply H.
+ destruct H as [H H1].
  destruct H1 as [H1 H2]. apply H1.
+ destruct H as [H H1].
  destruct H1 as [H1 H2]. apply H2.
Qed.


Lemma A_m_lt_A_M (mal : nat -> D ->R) (init: D -> R) (A: D -> bool):
   forall (A_m A_M: R),
   F_totally_bounded_general A ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq (fun t:nat => m_general mal init A t) A_m ->
  is_lim_seq (fun t:nat => M_general mal init A  t) A_M ->
  A_m <> A_M ->
  (A_m < A_M)%Re.
Proof.
intros.
assert ((forall t:nat, (m_general mal init A t <= M_general mal init A t)%Re) ->
        is_lim_seq (fun t: nat => m_general mal init A t) A_m -> 
        is_lim_seq (fun t: nat => M_general mal init A  t) A_M ->
        (A_m <= A_M)%Re).
{ apply is_lim_seq_le. } 
assert (forall t : nat, (m_general mal init A t <= M_general mal init A t)%Re).
{ by apply order_m. }
specialize (H4 H5).
specialize (H4 H1 H2). nra. 
Qed.


Lemma sandwich_x (mal : nat -> D -> R) (init : D -> R) (A : D -> bool):
   forall (A_M A_m:R),
  is_lim_seq (fun t:nat => m_general mal init  A t ) A_m ->
  is_lim_seq (fun t:nat => M_general mal init A t) A_M ->
  A_M = A_m -> 
  exists L : Rbar,
    forall i : D,
    i \in Normal_general A -> is_lim_seq ((x_general mal init A)^~ i) L.
Proof.
intros. apply sandwich_func with (fun t:nat => m_general mal init A t)
       (fun t:nat => M_general mal init A t) .
exists A_M. intros. split.
+ by apply x_bound.
+ split.
  - rewrite H1. apply H.
  - apply H0.
Qed.


Lemma M_A_M_lower_bound (mal : nat -> D ->R) (init : D -> R) (A: D -> bool):
  forall (A_M : R),
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A  mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq (fun t:nat => M_general mal init A t) A_M ->
  forall t:nat, (A_M <= M_general mal init A t)%Re.
Proof.
intros.
apply (is_lim_seq_decr_compare (fun t:nat => M_general mal init A t) A_M).
+ apply H2. 
+ destruct H. by apply A_M_monotonic.
Qed.

Lemma m_A_m_lower_bound  (mal : nat ->D->R) (init: D -> R) (A : D -> bool):
 forall (A_m : R),
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq (fun t:nat => m_general mal init A t) A_m ->
  forall t:nat, (m_general mal init A t <= A_m)%Re.
Proof.
intros.
apply (is_lim_seq_incr_compare (fun t:nat => m_general mal init A t) A_m).
+ apply H2. 
+ intros. apply Rge_le. destruct H. by apply A_m_monotonic.
Qed.


Lemma posreal_cond: forall (x:posreal), (0< x)%Re.
Proof.
intros. destruct x. auto.
Qed.


Lemma max_bound (A_M:R) (mal : nat ->D ->R) (init: D ->R) (A : D -> bool):
  F_totally_bounded_general A  ->
  (0 < F + 1 <= #|D|)%N ->
  (exists t:nat , forall (i:D), 
    i \in Normal_general A -> (x_general mal init A t i < A_M)%Re) ->
   exists t:nat, (M_general mal init A  t < A_M)%Re.
Proof.
intros. destruct H1 as [t H1]. exists t.
rewrite /M_general. apply bigmax_lt.
+ rewrite size_map. destruct H. by apply size_normal_gt_0.
+ intros. rewrite size_map in H2.
  specialize (H1 (nth key (enum (Normal_general A)) i)).
  assert (nth key (enum (Normal_general A)) i \in (Normal_general A) ).
  { by apply nth_normal. } specialize (H1 H3).
  assert (x_general mal init A t (nth key (enum (Normal_general A)) i) = 
          [seq x_general mal init A t i | i <- enum (Normal_general A)]`_i ).
  { assert ( [seq x_general mal init A t i | i <- enum (Normal_general A)]`_i = 
                 (fun i:D => (x_general mal init A t i)) (nth key (enum (Normal_general A)) i)).
    { by apply nth_map. } by rewrite H4.
  } rewrite -H4. by apply H1.
Qed.

Lemma min_bound (A_m:R) (mal : nat -> D ->R) (init : D -> R) (A: D -> bool):
   F_totally_bounded_general A ->
  (0 < F + 1 <= #|D|)%N ->
  (exists t:nat , forall (i:D), 
    i \in Normal_general A -> (x_general mal init A t i > A_m)%Re) ->
   exists t:nat, (m_general mal init A t > A_m)%Re.
Proof.
intros. destruct H1 as [t H1]. exists t.
rewrite /m_general. 
assert (A_m = (- - A_m)%Re). { by rewrite Ropp_involutive. }
rewrite H2. apply Ropp_lt_gt_contravar.
apply bigmax_lt.
+ rewrite size_map. destruct H. by apply size_normal_gt_0.
+ intros. rewrite size_map in H3.
  specialize (H1 (nth key (enum (Normal_general A)) i)).
  assert (nth key (enum (Normal_general A)) i \in (Normal_general A) ).
  { by apply nth_normal. } specialize (H1 H4).
  assert (- x_general mal init A t (nth key (enum (Normal_general A)) i) = 
          [seq - (x_general mal init A t i) | i <- enum (Normal_general A)]`_i ).
  { assert ( [seq - (x_general mal init A t i) | i <- enum (Normal_general A)]`_i = 
                 (fun i:D => - (x_general mal init A t i)) (nth key (enum (Normal_general A)) i)).
    { by apply (@nth_map D key R 0%Re (fun i:D => - (x_general mal init A t i)) i (enum (Normal_general A))) . }
    by rewrite H5.
  } rewrite -H5. by apply Ropp_gt_lt_contravar , H1.
Qed.


Fixpoint eps_j (m:nat) (eps_0 eps: posreal) (a:R) : R:=
  match m with
  | O => eps_0
  | S n => (a * (eps_j n eps_0 eps a) - (1 - a)* eps)%Re
  end.


Lemma eps_j_expand (j:nat) (eps_0 eps: posreal) (a:R):
  (eps_j j eps_0 eps a) = (a^j * eps_0 - (1 - a^j) * eps)%Re.
Proof.
induction j.
+ rewrite /eps_j. rewrite !RpowE expr0//=.
  rewrite Rmult_1_l.
  assert ( (1-1)%Re = 0%Re). { nra. } rewrite H.
  rewrite Rmult_0_l. by rewrite RminusE subr0.
+ simpl. rewrite IHj. 
  assert ((a * (a ^ j * eps_0 - (1 - a ^ j) * eps) - (1 - a) * eps)%Re = 
          (a * a ^ j * eps_0 - ( a * (1 - a^j) +  (1-a)) * eps)%Re).
  { nra. } rewrite H. clear H.
  apply Rplus_eq_compat_l, Ropp_eq_compat, Rmult_eq_compat_r.
  nra.
Qed.



Lemma a_j_pow_gt_0: forall (j:nat) (a:R),
  (0 < a)%Re -> (0<j)%N ->
  (a ^ j > 0)%Re.
Proof.
intros. induction j.
+ by [].
+ assert ((0<=j)%N). { by []. } rewrite leq_eqVlt in H1.
  assert ((0%N == j) \/ (0 < j)%N). { by apply /orP. }
  destruct H2.
  - rewrite eq_sym in H2. assert (j = 0%N). { by apply /eqP. }
    rewrite H3. nra.
  - specialize (IHj H2). rewrite RpowE. rewrite exprS -RmultE -RpowE.
    apply Rmult_lt_0_compat; nra.
Qed.
  
Lemma a_j_pow_lt_l: forall (j:nat) (a:R),
  (0 < a)%Re -> (a < 1)%Re -> (0<j)%N ->
  (a ^ j < 1)%Re.
Proof.
intros. induction j.
+ by [].
+ assert ((0<=j)%N). { by []. } rewrite leq_eqVlt in H2.
  assert ((0%N == j) \/ (0 < j)%N). { by apply /orP. }
  destruct H3.
  - rewrite eq_sym in H3. assert (j = 0%N). { by apply /eqP. }
    rewrite H4. nra.
  - specialize (IHj H3). rewrite RpowE. rewrite exprS -RmultE -RpowE.
    assert (1%Re = (1 * 1)%Re). { nra. } rewrite H4.
    apply Rmult_gt_0_lt_compat.
    * by apply a_j_pow_gt_0.
    * nra.
    * nra.
    * nra.
Qed.


Lemma a_j_pow_le_rel:forall (j N:nat) (a:R),
  (0 < a)%Re -> (a < 1)%Re -> (0<j)%N -> (0<N)%N-> (j <= N)%N ->
  (a ^ j >= a ^ N)%Re.
Proof.
intros. induction N.
+ rewrite leqn0 in H3.
  assert (j = 0%N). { by apply /eqP. } rewrite H4. nra.
+ rewrite leq_eqVlt in H3.
  assert ((j == N.+1) \/ (j < N.+1)%N). { by apply /orP. }
  destruct H4.
  - assert (j = N.+1). { by apply /eqP. } rewrite H5. nra.
  - apply ltnSE in H4.
    assert ((0 <= N)%N). { by []. } rewrite leq_eqVlt in H5.
    assert ((0%N == N) \/ (0 < N)%N). { by apply /orP. }
    destruct H6.
    * rewrite eq_sym in H6. assert (N = 0%N). { by apply /eqP. }
      rewrite H7 in H4. rewrite leqn0 in H4.
      assert (j = 0%N). { by apply /eqP. } by rewrite H8 in H1.
    * apply Rge_trans with (a^N)%Re.
      ++ by apply IHN.
      ++ assert ( (a ^ N)%Re = (1 * a ^ N)%Re). { nra. }
         rewrite H7. rewrite !RpowE exprS -RmultE.
         apply Rmult_ge_compat_r.
         - apply Rle_ge, Rlt_le. rewrite -RpowE. by apply a_j_pow_gt_0.
         - nra.
Qed.


Lemma eps_j_gt_0: forall (j N:nat) (eps_0 eps: posreal) (a:R),
  (0<N)%N-> (j<=N)%N -> 
  (0 < a)%Re /\ (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (0 < eps_j j eps_0 eps a)%Re.
Proof.
intros. destruct H1.
assert ((0<=j)%N). { by []. } rewrite leq_eqVlt in H4.
assert ((0%N == j) \/ (0 < j)%N). { by apply /orP. }
destruct H5.
+ rewrite eq_sym in H5. assert (j=0%N). { by apply /eqP. }
  rewrite H6 //=. apply posreal_cond.
+ rewrite eps_j_expand.
apply Rlt_Rminus.
assert ((a ^ j * eps_0)%Re = ((1 - a ^ j) * ((a ^ j / (1 - a ^ j))* eps_0))%Re).
{ assert (((1 - a ^ j) * (a ^ j / (1 - a ^ j) * eps_0))%Re = 
           ((a ^ j * ((1 - a ^ j) / (1 - a ^ j))) * eps_0)%Re).
  { nra. } rewrite H6.
  apply Rmult_eq_compat_r. assert ((a^j * 1)%Re = (a^j)%Re). { nra. }
  rewrite -[LHS]H7. apply Rmult_eq_compat_l.
  symmetry. apply Rinv_r.
  assert ((0 < (1 - a ^ j)%Re)%Re -> (1 - a ^ j)%Re <> 0%Re).
  { nra. } apply H8. apply Rlt_Rminus. by apply a_j_pow_lt_l.
}
rewrite H6.  apply Rmult_lt_compat_l.
+ apply Rlt_Rminus.  by apply a_j_pow_lt_l.
+ apply Rlt_le_trans with ((a ^ N / (1 - a ^ N)) *eps_0)%Re.
  - by [].
  - apply Rmult_le_compat_r .
    * apply Rlt_le. apply posreal_cond.
    * apply Rmult_le_compat.
      ++ by apply Rlt_le, a_j_pow_gt_0.
      ++ by apply Rlt_le, Rinv_0_lt_compat, Rlt_Rminus, a_j_pow_lt_l.
      ++ by apply Rge_le, a_j_pow_le_rel.
      ++ assert ((/ (1 - a ^ N))%Re = (1 * / (1 - a ^ N))%Re).  { nra. }
         rewrite H7.
         assert ((/ (1 - a ^ j))%Re = ((/ (1 - a ^ j) * (1 - a ^ N)) * (/(1 - a ^ N)))%Re).
         { assert ((/ (1 - a ^ j) * (1 - a ^ N) * / (1 - a ^ N))%Re = 
                    (/ (1 - a ^ j) * ((1 - a ^ N) * / (1 - a ^ N)))%Re).
           { nra. } rewrite H8.
           assert (((1 - a ^ N) * / (1 - a ^ N))%Re = 1%Re).
           { apply Rinv_r.
             assert ((0< (1 - a ^ N))%Re -> (1 - a ^ N)%Re <> 0%Re). { nra. }
             apply H9. apply Rlt_Rminus. by apply a_j_pow_lt_l.
           } rewrite H9. nra.
         }
         rewrite H8. apply Rmult_le_compat_r .
         - apply Rlt_le. apply Rinv_0_lt_compat.
           apply Rlt_Rminus. by apply a_j_pow_lt_l.
         - assert (1%Re = (/ (1 - a ^ j) * (1 - a ^ j))%Re).
           { symmetry. apply Rinv_l.
             assert ((0< (1 - a ^ j))%Re -> (1 - a ^ j)%Re <> 0%Re).
             { nra. } apply H9. apply Rlt_Rminus. by apply a_j_pow_lt_l.
           } 
           assert (((/ (1 - a ^ j) * (1 - a ^ j))%Re <= / (1 - a ^ j) * (1 - a ^ N))%Re ->
                     (1 <= / (1 - a ^ j) * (1 - a ^ N))%Re).
           { by rewrite -H9; nra. } apply H10.
           apply Rmult_le_compat_l.
           * apply Rlt_le. apply Rinv_0_lt_compat.
             apply Rlt_Rminus. by apply a_j_pow_lt_l. 
           * apply Rplus_le_compat_l, Ropp_ge_le_contravar.
             by apply a_j_pow_le_rel.
Qed.


Lemma eps_j_lt_j_minus_1 (j:nat) (a:R) (eps_0 eps: posreal)
  (mal : nat -> D ->R) (init : D->R) (A: D -> bool):
  F_totally_bounded_general A ->
  (0 < F + 1 <= #|D|)%N ->
  let N:= #|Normal_general A| in  
  (0<j)%N -> (0<a)%Re -> (a < 1)%Re -> (j<= N)%N ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (eps_j j eps_0 eps a < eps_j (j - 1) eps_0 eps a)%Re.
Proof.
intros.
assert ( j = (j-1).+1). { rewrite subn1. by rewrite prednK. }
assert (eps_j j eps_0 eps a = eps_j (j - 1).+1 eps_0 eps a).
{ by rewrite [in LHS]H6. }
assert (eps_j (j - 1) eps_0 eps a  = (a * eps_j (j - 1) eps_0 eps a +
          (1-a) * eps_j (j - 1) eps_0 eps a)%Re).
{ nra. } 
rewrite H7 H8//=.
apply Rplus_lt_compat_l. apply Rlt_trans with 0%Re.
+ apply Ropp_0_lt_gt_contravar. apply Rmult_lt_0_compat.
  - nra.
  - apply posreal_cond.
+ apply Rmult_lt_0_compat.
  - nra.
  - assert ((0 < N)%N). { rewrite /N cardE. by apply size_normal_gt_0. }
    apply eps_j_gt_0 with N.
    * by [].
    * apply leq_trans with j.
      ++ rewrite subn1. apply leq_pred.
      ++ by [].
    * by [].
    * by [].
Qed.

Lemma card_decreases (S1 S2: {set D}): 
  (exists i:D, i \in S1 /\ i \notin S2) -> 
   S2 \subset S1 ->
  (#|S2| < #|S1|)%N.
Proof.
intros. apply proper_card.
rewrite /proper. apply /andP.
split.
+ by [].
+ destruct H as [i H]. destruct H.
  apply /subsetPn. by exists i.
Qed.


Lemma X_M_normal_exists (t_eps: nat) (A_M: R) (eps_0:posreal)
  (mal : nat -> D ->R) (init : D -> R) (A: D -> bool): 
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta M_general mal init A] A_M ->
    exists i:D, i \in (X_M_t_e_i eps_0 A_M t_eps mal init A) /\ i \in Normal_general A.
Proof.
intros. 
assert (M_general mal init A t_eps \in map (fun i:D => x_general mal init A t_eps i) (enum (Normal_general A))).
{ rewrite /M_general. 
  apply (@bigmaxr_mem _ 0%Re (map (fun i:D => x_general mal init A t_eps i) (enum (Normal_general A)))).
  rewrite size_map. destruct H. by apply size_normal_gt_0.
} 
assert (exists2 i:D, i \in (enum (Normal_general A)) &
            (M_general mal init A t_eps = (fun i:D => x_general mal init A t_eps i) i)).
{ by apply /mapP. }
destruct H4 as [i H4]. exists i.
split.
+ rewrite inE. rewrite -H5.
  destruct (Rgt_dec (M_general mal init A t_eps) (A_M - eps_0)).
  - by simpl.
  - simpl. 
    assert ((A_M - eps_0 < M_general mal init A t_eps)%Re).
    { apply Rlt_le_trans with (A_M - 0)%Re.
      + apply Rplus_lt_compat_l. apply Ropp_gt_lt_contravar.
        apply posreal_cond.
      + assert ((A_M - 0)%Re = A_M). { nra. }
        rewrite H6. destruct H. by apply M_A_M_lower_bound.
    }
    contradiction.
+ by apply in_enum_Normal.
Qed. 

Lemma X_m_normal_exists (t_eps: nat) (A_m: R) (eps_0:posreal)
  (mal : nat -> D ->R) (init : D ->R) (A: D -> bool): 
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init  ->
  (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta m_general mal init A] A_m ->
    exists i:D, i \in (X_m_t_e_i eps_0 A_m t_eps mal init A) /\ i \in Normal_general A.
Proof.
intros. 
assert ((-(m_general mal init A t_eps)) \in map (fun i:D => - x_general mal init A t_eps i) (enum (Normal_general A))).
{ rewrite /m_general. rewrite -RoppE. rewrite Ropp_involutive.
  apply (@bigmaxr_mem _ 0%Re (map (fun i:D => - x_general mal init A t_eps i) (enum (Normal_general A)))).
  rewrite size_map. destruct H. by apply size_normal_gt_0.
} 
assert (exists2 i:D, i \in (enum (Normal_general A)) &
            (- (m_general mal init A t_eps) = (fun i:D => - x_general mal init A t_eps i) i)).
{ by apply /mapP. }
destruct H4 as [i H4]. exists i.
split.
+ rewrite inE.
  assert (m_general mal init A t_eps = x_general mal init A t_eps i). 
  { rewrite -[LHS]Ropp_involutive. rewrite !RoppE. rewrite H5.
    by rewrite -!RoppE Ropp_involutive.
  } rewrite -H6.
  destruct (Rlt_dec (m_general mal init A t_eps) (A_m + eps_0)).
  - by simpl.
  - simpl. 
    assert ((m_general mal init A t_eps < A_m + eps_0)%Re).
    { apply Rle_lt_trans with (A_m + 0)%Re.
      + assert ((A_m + 0)%Re = A_m). { nra. }
        rewrite H7. by apply m_A_m_lower_bound.
      + apply Rplus_lt_compat_l. 
        apply posreal_cond.
    }
    contradiction.
+ by apply in_enum_Normal.
Qed.

 
Lemma sum_f_R0_big_equiv (F:nat -> R) (n:nat):
  sum_f_R0 F n = \big[+%R/0]_(j<n.+1) F j.
Proof.
induction n.
+ by rewrite /sum_f_R0 big_ord_recr big_ord0 //= add0r.
+ simpl. rewrite big_ord_recr //= IHn. by rewrite RplusE.
Qed.

Lemma big_nat_split (i:D) (l : seq D) (F: nat -> R):
  \sum_(i0 < (size l - 1).+1 | i0 != inord (index i l)) F i0 =
   \sum_(i0 < (size l - 1).+1 | (i0 != inord (index i l)) && 
                (i0 < (@inord (size l- 1) (index i l)))%N) F i0 + 
    \sum_(i0 < (size l - 1).+1 | (i0 != inord (index i l)) && 
                ~~(i0 < (@inord (size l - 1) (index i l)))%N) F i0.
Proof.
apply bigID.
Qed.

Lemma P_and_false: forall (P : bool),
  P && false = false.
Proof.
intros. by destruct P.
Qed.

Lemma P_implies_and_true: forall (P Q:bool),
  P -> (P || Q) && P = P.
Proof.
intros. by destruct P.
Qed.

Lemma notP_implies_and_true: forall (P Q: bool),
  ~~P -> (P || Q) && P = P.
Proof.
intros. destruct P.
+ by [].
+ by destruct Q.
Qed.


Lemma not_eq: forall (n:nat), n != n = false.
Proof.
intros. rewrite neq_ltn. by rewrite ltnn.
Qed.

Lemma big_cond_simpl_lt (i:D) (l : seq D) (F: nat -> R):
  \sum_(i0 < (size l - 1).+1 | (i0 != inord (index i l)) && 
                (i0 < (@inord (size l- 1) (index i l)))%N) F i0 = 
  \sum_(i0 < (size l - 1).+1 | (i0 < (@inord (size l- 1) (index i l)))%N) F i0.
Proof.
apply eq_bigl. unfold eqfun. intros.
assert ((x <= (@inord (size l- 1) (index i l)))%N \/ (x >= (@inord (size l- 1) (index i l)))%N).
{ apply /orP. apply leq_total. } destruct H.
+ rewrite leq_eqVlt in H. 
  assert ((x == (@inord (size l- 1) (index i l))) \/ (x < (@inord (size l- 1) (index i l)))%N).
  { by apply /orP. } destruct H0.
  - assert (x = (@inord (size l- 1) (index i l))). { by apply /eqP. }
    rewrite H1. rewrite ltnn. by rewrite not_eq. 
  - rewrite neq_ltn. by apply P_implies_and_true.
+ rewrite leqNgt in H. rewrite neq_ltn. by apply notP_implies_and_true. 
Qed. 

Lemma P_implies_and_true_R: forall (P Q S: bool),
  P -> (P || Q) && ~~P = ~~(S || P).
Proof.
intros. destruct P.
+ simpl. by destruct S.
+ by []. 
Qed.


Lemma notP_implies_and_true_R: forall (P Q S: bool),
  (Q = ~~S) -> 
  ~~P -> (P || Q) && ~~P = ~~(S || P).
Proof.
intros. destruct P.
+ by simpl. 
+ simpl. simpl in H0. destruct Q.
  - simpl. destruct S.
    * simpl. by simpl in H. 
    * by simpl.
  - simpl. destruct S.
    *  by simpl.
    * simpl. by simpl in H.
Qed.

Lemma n_leq_true: forall (n:nat), (n<=n)%N = true.
Proof.
intros. by rewrite leqnn.
Qed.

Lemma P_solves: forall (P Q S: bool),
  (Q -> ~~S) ->  
  (Q || P) && (S || P) = P.
Proof.
intros. destruct P.
+ simpl. destruct S.
  - simpl. simpl in H.
    by destruct Q.
  - simpl. simpl in H. by destruct Q. 
+ simpl. destruct S.
  - simpl. simpl in H.
    destruct Q.
    * simpl. assert (true). { by [].  } by specialize (H H0).
    * by simpl.
  - simpl. simpl in H. by destruct Q.
Qed.


Lemma big_cond_simpl_gt (i:D) (l : seq D) (F: nat -> R):
  \sum_(i0 < (size l - 1).+1 | (i0 != inord (index i l)) && 
                ~~(i0 < (@inord (size l- 1) (index i l)))%N) F i0 = 
  \sum_(i0 < (size l - 1).+1 | (i0 > (@inord (size l- 1) (index i l)))%N) F i0.
Proof.
apply eq_bigl. unfold eqfun. intros.
assert ((x <= (@inord (size l- 1) (index i l)))%N \/ (x >= (@inord (size l- 1) (index i l)))%N).
{ apply /orP. apply leq_total. } destruct H.
+ rewrite leq_eqVlt in H. 
  assert ((x == (@inord (size l- 1) (index i l))) \/ (x < (@inord (size l- 1) (index i l)))%N).
  { by apply /orP. } destruct H0.
  - assert (x = (@inord (size l- 1) (index i l))). { by apply /eqP. }
    rewrite H1. rewrite ltnn. simpl. by rewrite not_eq.
  - rewrite neq_ltn. rewrite [in RHS]ltnNge. rewrite [in RHS]leq_eqVlt.
    by apply P_implies_and_true_R.
+ rewrite -leqNgt. rewrite leq_eqVlt in H.
  assert (((@inord (size l- 1) (index i l))== x) \/ ((@inord (size l- 1) (index i l)) < x)%N).
  { by apply /orP. } destruct H0.
  - assert (x = (@inord (size l- 1) (index i l))). { rewrite eq_sym in H0.  by apply /eqP. }
    rewrite H1. simpl. by rewrite not_eq ltnn n_leq_true.
  - rewrite leq_eqVlt neq_ltn.
    assert ((x < (@inord (size l- 1) (index i l)))%N -> ~~((@inord (size l- 1) (index i l)) == x)).
    { intros. rewrite neq_ltn. apply /orP. by right. }
    by apply P_solves.
Qed.


Lemma big_sum_ge_ex_abstract I r (P: pred I) (E1 E2: I -> R):
  (forall i, P i -> (E1 i <= E2 i)%Re) ->
  (\big[+%R/0]_(i <-r | P i) E1 i <= \big[+%R/0]_(i <-r | P i) E2 i).
Proof.
move => leE12. apply /RleP. apply big_ind2.
+ nra.
+ intros. rewrite -!RplusE. by apply Rplus_le_compat.
+ apply leE12.
Qed.


Lemma x_val_at_neighbor (i:D) (a A_M:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init: D -> R) (A : D -> bool):
  forall k:D, k \in (in_neighbor i :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j)%N mal init A) ->
  (x_general mal init A (t_eps+j)%N k <= A_M - (eps_j j eps_0 eps a))%Re.
Proof.
intros. rewrite in_setD in H.
assert ((k \notin X_M_t_e_i (eps_j j eps_0 eps a) A_M
                (t_eps + j) mal init A) /\ (k \in in_neighbor i)).
{ by apply /andP. } destruct H0. rewrite inE in H0.
destruct (Rgt_dec (x_general mal init A (t_eps + j) k)
          (A_M - eps_j j eps_0 eps a)).
+ by simpl in H0.
+ simpl in H0. by apply Rnot_gt_le in n.
Qed.

Lemma x_left_ineq_1 (i:D) (a A_M:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat ->D ->R) (init : D ->R) (A: D -> bool):
   i \in Normal_general A -> (0 < a)%Re -> (a < 1)%Re ->
  (x_general mal init A (t_eps + j) i <= A_M - eps_j j eps_0 eps a)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
      (i0 < (@inord  (size incl - 1) (index i incl)))%N) 
    (x_general mal init A (t_eps + j) (nth i incl i0) *
     w (t_eps + j) (i, nth i incl i0))%Re <=
 (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
      (i0 < (@inord  (size incl - 1) (index i incl)))%N)
     w (t_eps + j) (i, nth i incl i0)) *
    (A_M - eps_j j eps_0 eps a))%Re.
Proof.
intros. rewrite (@big_cond_simpl_lt i incl (fun i0:nat => (x_general mal init A (t_eps + j) (nth i incl i0) *
                    w (t_eps + j) (i, nth i incl i0))%Re)).
rewrite (@big_cond_simpl_lt i incl (fun i0:nat =>  w (t_eps + j) (i, nth i incl i0))).
apply /RleP.
assert (((\sum_(i0 < (size incl - 1).+1 | 
              (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                 w (t_eps + j) (i, nth i incl i0)) *
             (A_M - eps_j j eps_0 eps a))%Re = 
          \sum_(i0 < (size incl - 1).+1 | 
              (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                 ((w (t_eps + j) (i, nth i incl i0)) *
             (A_M - eps_j j eps_0 eps a))%Re).
{ by rewrite big_distrl //=. } rewrite H4.
apply big_sum_ge_ex_abstract.
intros. rewrite Rmult_comm. apply Rmult_le_compat_l.
+ apply Rle_trans with a.
  - by apply Rlt_le.
  - apply H3. apply mem_nth.
    apply ltn_leq_trans with (size incl - 1).+1.
    ++ by apply ltn_ord.
    ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
       rewrite ltn_subrL. apply /andP. split.
       - by [].
       - apply H6.
+ apply Rle_trans with (x_general mal init A (t_eps + j) i).
  - assert (sorted_Dseq_general (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)%N)).
    { apply lemma_1.incl_sorted_general. } rewrite /sorted_Dseq_general in H6.
    apply H6.
    * rewrite -/incl. apply mem_nth.
      apply ltn_leq_trans with (size incl - 1).+1.
      ++ by apply ltn_ord.
      ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
         rewrite ltn_subrL. apply /andP. split.
         - by [].
         - apply H7.
    * apply i_in_incl_general.
  - rewrite index_uniq.
    * rewrite -/incl. rewrite inordK in H5.
      ++ apply H5.
      ++ rewrite subn1. rewrite prednK.
         - rewrite index_mem. apply i_in_incl_general.
         - apply size_incl_not_0_general.
    * apply ltn_leq_trans with (size incl - 1).+1.
      ++ by apply ltn_ord.
      ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
         rewrite ltn_subrL. apply /andP. split.
         - by [].
         - apply H7.
    * apply incl_uniq_general.
+ by [].
Qed.



Lemma and_conv: forall (P Q R: bool),
  P && Q && R -> (P /\ Q /\ R).
Proof.
intros. destruct P.
+ destruct Q.
  - destruct R2.
    * by [].
    * by [].
  - by [].
+ by [].
Qed.


Lemma R_i_gt_val_rel (i:D) (t:nat) (mal: nat -> D -> R) (init : D -> R) (A: D -> bool) :
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
  forall j k:D, 
    k \in incl -> 
     j \in (R_i_greater_than_general mal init A i t) ->
      (x_general mal init A t k <= x_general mal init A t j)%Re.
Proof.
intros. rewrite /R_i_greater_than_general in H0.
rewrite inE in H0. apply and_conv in H0. destruct H0.
destruct H1.
destruct (Rgt_dec (x_general mal init A t j) (x_general mal init A t i)).
+ simpl in H0.
  rewrite /incl / incl_neigh_minus_extremes /remove_extremes in H.
  rewrite mem_filter in H. apply and_conv in H. destruct H.
  destruct H3.
  assert (Rle_dec (x_general mal init A t k) (x_general mal init A t i)
             \/ (index k (inclusive_neighbor_list i) <=
                 size (inclusive_neighbor_list i) - F - 1)%N).
  { by apply /orP. } destruct H5.
  - destruct (Rle_dec (x_general mal init A t k) (x_general mal init A t i)).
    * simpl in H5. apply Rle_trans with (x_general mal init A t i).
      ++ apply r0.
      ++ by apply Rlt_le.
    * by simpl in H5.
  - assert (sorted_Dseq_general (inclusive_neighbor_list i)).
    { by apply lemma_1.inclusive_neighbors_sorted_general. } rewrite /sorted_Dseq_general in H6.
    apply H6.
    - apply H4.
    - apply H2.
    - by apply leq_ltn_trans with (size (inclusive_neighbor_list i) - F - 1)%N.
+ by simpl in H0.
Qed.


Lemma exists_an_elem_in_out_set (i:D) (t:nat)
  (mal : nat -> D -> R) (init : D -> R) (A : D -> bool):
  F_total_malicious_general mal init A -> 
  R_i_greater_than_general mal init A i t != Adversary_general A -> 
  #|R_i_greater_than_general mal init A i t| == F ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
  forall i0 : 'I_(size incl - 1).+1, 
  nth i incl i0 \in Adversary_general A ->
  exists k:D, k \in (Normal_general A :&: (R_i_greater_than_general mal init A i t)).
Proof.
intros.
assert (exists (j:D), (j \in Normal_general A) /\ (j \in R_i_greater_than_general mal init A i t)).
{ by apply exists_normal_node_in_R_i_gt_general. }
destruct H3 as [j H3]. exists j.
rewrite in_setI. by apply /andP.
Qed.



Lemma not_in_R_i_greater_than (i j:D) (t:nat)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
    (j \in incl \/ j \in R_i_less_than_general mal init A i t) ->
      (j \notin R_i_greater_than_general mal init  A i t).
Proof.
intros. destruct H.
+ rewrite inE. rewrite /incl /incl_neigh_minus_extremes /remove_extremes in H.
  rewrite mem_filter in H. apply and_conv in H.
  destruct H. destruct H0.
  apply /nandP. left.
  apply /nandP. 
  assert (Rle_dec (x_general mal init A t j) (x_general mal init A t i)
             \/ (index j (inclusive_neighbor_list i) <=
                 size (inclusive_neighbor_list i) - F - 1)%N).
  { by apply /orP. } destruct H2.
  - left. destruct (Rle_dec (x_general mal init A t j) (x_general mal init A t i)).
    * simpl in H2. 
      destruct (Rgt_dec (x_general mal init A t j) (x_general mal init A t i)).
      ++ simpl. apply Rgt_not_le in r0. contradiction.
      ++ by simpl.
    * simpl in H2. by [].
  - right. by rewrite -leqNgt.
+ rewrite inE. rewrite inE in H. apply and_conv in H.
  destruct H. destruct H0. apply /nandP. left.
  apply /nandP. left.
  destruct (Rlt_dec (x_general mal init A t j) (x_general mal init A t i)).
  - destruct (Rgt_dec (x_general mal init A t j) (x_general mal init A t i)).
    * simpl. apply Rgt_asym in r0. contradiction.
    * by simpl in H.
  - by simpl in H.
Qed.


Lemma incl_does_not_contain_adversary (i:D) (t:nat)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
  forall (i0 : 'I_(size incl - 1).+1), 
  R_i_greater_than_general mal init A i t == Adversary_general A ->
                  nth i incl i0 \notin Adversary_general A.
Proof.
intros. rewrite -Normal_adversary_disjoint_general.
rewrite Normal_not_adversary.
assert (R_i_greater_than_general mal init A i t = Adversary_general A).
{ by apply /eqP. } rewrite -H0. 
rewrite in_setC. 
apply (@not_in_R_i_greater_than  i (nth i incl i0) t mal init A).
left. rewrite -/incl. 
apply mem_nth.
apply ltn_leq_trans with (size incl - 1).+1.
- by apply ltn_ord.
- assert ((0< size incl)%N). { apply size_incl_not_0_general. }
  rewrite ltn_subrL. apply /andP. split.
  * by [].
  * apply H1.
Qed.


Lemma x_right_ineq_1 (i:D) (a A_M:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D ->R) (init: D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
     ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
        (x_general mal init A (t_eps + j) (nth i incl i0) *
         w (t_eps + j) (i, nth i incl i0))%Re <=
 (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
    ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
       w (t_eps + j) (i, nth i incl i0)) * M_general mal init A (t_eps + j))%Re.
Proof.
intros. rewrite (@big_cond_simpl_gt i incl (fun i0:nat => (x_general mal init A (t_eps + j) (nth i incl i0) *
                    w (t_eps + j) (i, nth i incl i0))%Re)).
rewrite (@big_cond_simpl_gt i incl (fun i0:nat =>  w (t_eps + j) (i, nth i incl i0))).
apply /RleP.
assert (((\sum_(i0 < (size incl - 1).+1 | 
              ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                 w (t_eps + j) (i, nth i incl i0)) *
             M_general mal init A (t_eps + j))%Re = 
          \sum_(i0 < (size incl - 1).+1 | 
             ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                 ((w (t_eps + j) (i, nth i incl i0)) *
             M_general mal init A (t_eps + j))%Re).
{ by rewrite big_distrl //=. } rewrite H4.
apply big_sum_ge_ex_abstract.
intros. rewrite Rmult_comm. apply Rmult_le_compat_l.
+ apply Rle_trans with a.
  - by apply Rlt_le.
  - apply H3. apply mem_nth.
    apply ltn_leq_trans with (size incl - 1).+1.
    ++ by apply ltn_ord.
    ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
       rewrite ltn_subrL. apply /andP. split.
       - by [].
       - apply H6.
+ assert ((nth i incl i0) \in Normal_general A \/ (nth i incl i0) \in Adversary_general A).
  { apply normal_or_adversary. }
  destruct H6.
  - by apply x_bound.
  - assert ((#|R_i_greater_than_general mal init A i (t_eps + j)%N| <= F)%N).
    { apply R_i_gt_bounded_general. } rewrite leq_eqVlt in H7.
    assert ( (#|R_i_greater_than_general mal init A i (t_eps + j)| == F)
              \/ (#|R_i_greater_than_general mal init A i (t_eps + j)| < F)%N).
    { by apply /orP. } destruct H8.
    * assert(R_i_greater_than_general mal init A i (t_eps + j) == Adversary_general A \/
                  R_i_greater_than_general mal init A i (t_eps + j) != Adversary_general A).
      { apply /orP.
        by destruct (R_i_greater_than_general mal init A i (t_eps + j) == Adversary_general A).
      } destruct H9.
      ++ assert (R_i_greater_than_general mal init A i (t_eps + j) == Adversary_general A ->
                  nth i incl i0 \notin Adversary_general A).
         { by apply incl_does_not_contain_adversary. } specialize (H10 H9). 
         assert (~ (nth i incl i0 \in Adversary_general A)).
         { by apply /negP. } contradiction.
      ++ assert (exists k:D, k \in (Normal_general A :&: (R_i_greater_than_general mal init A  i (t_eps+j)%N))).
        { by apply exists_an_elem_in_out_set with i0.  } destruct H10 as [k H10]. rewrite in_setI in H10.
        assert ((k \in Normal_general A) /\
                     (k \in R_i_greater_than_general mal init A i (t_eps + j))).
        { by apply /andP. } destruct H11.
        apply Rle_trans with (x_general mal init A(t_eps + j) k).
        * apply R_i_gt_val_rel with i.
          ++ rewrite -/incl. apply mem_nth.
             apply ltn_leq_trans with (size incl - 1).+1.
             + by apply ltn_ord.
             + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
               rewrite ltn_subrL. apply /andP. split.
               - by [].
               - apply H13.
          ++ apply H12.
        * by apply x_bound.
    * (** The last node has the value same as x_i(t) and since i is Normal,
        x_i <= M **)
      apply Rle_trans with (x_general mal init A (t_eps + j)%N (last (head i incl) (behead incl))).
      - apply last_incl_is_max_general. rewrite -/incl. apply mem_nth.
        apply ltn_leq_trans with (size incl - 1).+1.
        + by apply ltn_ord.
        + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
          rewrite ltn_subrL. apply /andP. split.
          - by [].
          - apply H9.
      - assert (((x_general mal init A (t_eps + j) (last (head i incl ) (behead incl ))) = (x_general mal init A (t_eps + j) i))%Re).
        { by apply card_R_i_gt_lt_F_exchange_last_general. } rewrite H9.
        by apply x_bound.
Qed.

Lemma a_iter_n_ge_0: forall (a:R) (n:nat),
  (0 < a)%Re -> (0 <= a*+n).
Proof.
intros. induction n.
+ by rewrite mulr0n.
+ rewrite mulrSr -RplusE. apply /RleP.
  apply Rplus_le_le_0_compat.
  - by apply /RleP.
  - nra.
Qed.

Lemma sum_ge_a: forall I r (P: pred I) (a:R),
  (0 < a)%Re -> has P r ->
  (a <= \big[+%R/0]_(i <-r | P i) a)%Re.
Proof.
intros. assert (a = (0+a)%Re). { nra. } rewrite H1.
rewrite big_const_seq iter_addr addr0.
assert ((0 + a)%Re *+ count P r = a *+ count P r).
{ by rewrite RplusE add0r. } rewrite H2.
assert (count P r = (count P r).-1.+1).
{ rewrite prednK.
  + by [].
  + by rewrite -has_count. 
} rewrite H3. rewrite mulrSr -RplusE. apply Rplus_le_compat_r.
apply /RleP. by apply a_iter_n_ge_0.
Qed.


(** i should not be the first element  of the incl list **)
Lemma w_ge_a_1 (i:D) (a:R) (t_eps j:nat)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  (0 < a)%Re -> (a < 1)%Re ->
  let incl := incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in 
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
  (0 < index i incl)%N -> 
  let w_il:= \sum_(i0 < (size incl - 1).+1 | 
          (i0 < @inord (size incl -1) (index i incl))%N)
             w (t_eps + j) (i, nth i incl i0) in 
 (a <= w_il)%Re. 
Proof.
intros. rewrite /w_il. 
apply Rle_trans with (\sum_(i0 < (size incl - 1).+1 |
           ((i0 < @inord (size incl - 1) (index i incl)))%N) a).
+ apply sum_ge_a.
  - by [].
  - apply /hasP. simpl.
    exists 0.
    * apply mem_index_enum. 
    * rewrite !inordK.
      ++ by [].  (*assert ((0<= index i incl)%N). { by []. } *)
      ++ rewrite subn1. rewrite !prednK.
         - rewrite index_mem. apply i_in_incl_general.
         -  apply size_incl_not_0_general.
+ apply /RleP. apply big_sum_ge_ex_abstract. intros.
  apply H1. apply mem_nth.
  apply ltn_leq_trans with (size incl - 1).+1.
  ++ by apply ltn_ord.
  ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
     rewrite ltn_subrL. apply /andP. split.
     - by [].
     - apply H5.
Qed.


Lemma P_and_true: forall (P Q: bool),
  Q = true ->
  P && Q = P.
Proof.
intros. rewrite H. by destruct P.
Qed. 



Lemma x_val_decreases_1 (i:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init: D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta M_general mal init A] A_M ->
  (0<N)%N-> (j<=N)%N -> 
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (x_general mal init A (t_eps + j) i <= A_M - eps_j j eps_0 eps a)%Re ->
  (x_general mal init A (t_eps + j.+1) i <=  A_M - eps_j j.+1 eps_0 eps a)%Re.
Proof.
intros. simpl. 
assert ((t_eps + j.+1)%N = (t_eps + j).+1).
{ by rewrite -addn1 addnA addn1. } rewrite H13.
simpl.
assert (A i = false).
{ rewrite !inE in H5. simpl in H5. 
  assert ( (A i != true) /\ true).
  { by apply /andP. } destruct H14. 
  by destruct (A i).
} rewrite H14 //=.
rewrite sum_f_R0_big_equiv. rewrite -/incl.
assert ((0 <= index i incl)%N). { by []. }
rewrite leq_eqVlt in H15.
assert ((0%N == index i incl) \/ (0 < index i incl)%N).
{ by apply /orP. } destruct H16.
++ rewrite (bigD1 (inord (index i incl))) //=.
   rewrite inordK.
   + rewrite nth_index.
     - rewrite -RplusE.
       assert (\sum_(i0 < (size incl - 1).+1 | i0
                                 != 
                                 inord
                                 (index i incl))
                (x_general mal init A (t_eps + j) (nth i incl i0) *
                 w (t_eps + j) (i, nth i incl i0))%Re  = \sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                 ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                    (x_general mal init A (t_eps + j) (nth i incl i0) *
                     w (t_eps + j) (i, nth i incl i0))%Re).
       { apply eq_big.
         + unfold eqfun. intros.
           assert (index i incl = 0%N). { symmetry. by apply /eqP. }
           rewrite H17. rewrite inordK.
           - rewrite -leqNgt. 
             assert ((0 <= x)%N = true). { by []. } rewrite H18.
             by destruct (x != inord 0).
           - rewrite subn1. rewrite prednK; apply size_incl_not_0_general.
         + by intros.
       } rewrite H17. clear H17.
       apply Rle_trans with
            (x_general mal init A (t_eps + j) i * w (t_eps + j) (i, i) +
              (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                              ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                  w (t_eps + j) (i, nth i incl i0)) * M_general mal init A (t_eps+j))%Re.
       * apply Rplus_le_compat_l.
         rewrite /incl. by apply x_right_ineq_1 with a.
       * apply Rle_trans with 
          ((A_M - eps_j j eps_0 eps a) * w (t_eps + j) (i, i) +
             (\sum_(i0 < (size incl - 1).+1 | 
              (i0 != @inord (size incl -1) (index i incl)) &&
              ~~ (i0 < @inord (size incl -1) (index i incl))%N)
                 w (t_eps + j) (i, nth i incl i0)) *
             M_general mal init A (t_eps + j))%Re.
         ++ apply Rplus_le_compat_r. apply Rmult_le_compat_r.
            + apply Rle_trans with a.
              - nra.
              - apply H9. apply i_in_incl_general.
            + by [].
         ++ assert (( A_M - (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re = 
                      ((1-a)* (A_M + eps) + a * (A_M - eps_j j eps_0 eps a))%Re).
            { nra. } rewrite H17.
            assert (\sum_(i0 < (size incl - 1).+1 | 
                      (i0 != @inord (size incl -1) (index i incl)) &&
                      ~~ (i0 < @inord (size incl -1) (index i incl))%N)
                         w (t_eps + j) (i, nth i incl i0) = 
                    (1 - w (t_eps + j) (i, i))%Re).
            { assert (\sum_(i0 < (size incl - 1).+1 | (i0
                                 != 
                                 @inord (size incl -1)
                                 (index i incl)) &&
                                ~~
                                (i0 <
                                 @inord (size incl-1)
                                 (index i incl))%N)
                         w (t_eps + j) (i, nth i incl i0) =
                      (1 - w (t_eps + j) (i, i))%Re <-> 
                      (w (t_eps + j) (i, i) + \sum_(i0 < (size incl - 1).+1 | (i0
                                 != 
                                 @inord (size incl -1)
                                 (index i incl)) &&
                                ~~
                                (i0 <
                                 @inord (size incl -1)
                                 (index i incl))%N)
                         w (t_eps + j) (i, nth i incl i0))%Re = 1%Re).
             { nra. } rewrite H18. clear H18.
             rewrite sum_f_R0_big_equiv in H10. rewrite -H10.
             rewrite [in RHS](bigD1 (@inord (size incl-1) (index i incl))) //=.
             rewrite inordK.
             + rewrite nth_index.
               - rewrite -[in RHS]RplusE. apply Rplus_eq_compat_l.
                 apply eq_big. unfold eqfun. intros. apply P_and_true.
                 assert (index i incl = 0%N). { symmetry. by apply /eqP. }
                 rewrite H18. by rewrite -leqNgt. by intros.
               - by apply i_in_incl_general.
             + rewrite subn1. rewrite prednK.
               - rewrite index_mem. apply i_in_incl_general.
               - apply size_incl_not_0_general.
            } rewrite H18.
            assert ((M_general mal init A (t_eps+j)%N < A_M + eps)%Re). 
            { apply H11. apply /leP. apply leq_addr. }
            remember  (w (t_eps + j) (i, i)) as w_ii.
            apply Rle_trans with ((1 - a) * M_general mal init A (t_eps + j)%N +
                                      a * (A_M - eps_j j eps_0 eps a))%Re.
            - assert (((A_M - eps_j j eps_0 eps a) * w_ii +
                        (1 - w_ii) * M_general mal init A (t_eps + j))%Re = 
                        (M_general mal init A (t_eps + j) - w_ii * ( M_general mal init A (t_eps + j) - (A_M - eps_j j eps_0 eps a)))%Re).
              { nra. } rewrite H20.
                assert (((1 - a) * M_general mal init A (t_eps + j) +
                            a * (A_M - eps_j j eps_0 eps a))%Re = 
                         (M_general mal init A (t_eps + j) - a * (M_general mal init A (t_eps + j) - (A_M - eps_j j eps_0 eps a)))%Re).
                { nra. } rewrite H21.
                apply Rplus_le_compat_l, Ropp_ge_le_contravar.
                apply Rmult_ge_compat_r.
                * apply Rge_minus, Rle_ge. apply Rle_trans with A_M.
                  ++ assert ((0 < eps_j j eps_0 eps a)%Re).
                     { by apply eps_j_gt_0 with N. } nra.
                  ++ by apply M_A_M_lower_bound. 
                * apply Rle_ge. rewrite Heqw_ii. apply H9. apply i_in_incl_general.
              - apply  Rplus_le_compat_r, Rmult_le_compat_l.
                + nra. 
                + by apply Rlt_le.
     - apply i_in_incl_general.
   + rewrite subn1. rewrite prednK.
     - rewrite index_mem. apply i_in_incl_general.
     - apply size_incl_not_0_general.
++ rewrite (bigD1 (inord (index i incl))) //=. 
  rewrite inordK.
  + rewrite nth_index. 
    - rewrite -RplusE. 
      apply Rle_trans with ((M_general mal init A  (t_eps +j)%N) * w (t_eps + j) (i, i) +
           \sum_(i0 < (size incl - 1).+1 | 
           i0 != inord (index i incl))
              (x_general mal init A (t_eps + j) (nth i incl i0) *
               w (t_eps + j) (i, nth i incl i0))%Re).
      * apply Rplus_le_compat_r, Rmult_le_compat_r.
        ++ specialize (H9 i).
           assert (i \in incl). {  apply i_in_incl_general. }
           specialize (H9 H17).
           apply Rlt_le. by apply Rlt_le_trans with a.
        ++ by apply x_bound.
      * rewrite -RplusE -RmultE.
        (** break into two parts:
            1. i0 < inord (index i incl) : x_t i <= A_M - eps_j
            2. i0 > inord (index i incl): x_t i <= M
         **)
        rewrite (@big_nat_split i incl  
                  (fun i0 :nat => (x_general mal init A (t_eps + j) (nth i incl i0) *
                      w (t_eps + j) (i, nth i incl i0))%Re)).
        apply Rle_trans with
        (M_general mal init A (t_eps + j) * w (t_eps + j) (i, i) +  
          (((\sum_(i0 < (size incl - 1).+1 | 
                (i0 != (@inord  (size incl - 1) (index i incl))) &&
                (i0 < (@inord (size incl - 1) (index i incl)))%N)
                    w (t_eps + j) (i, nth i incl i0)) * (A_M - eps_j j eps_0 eps a))%Re +
          (\sum_(i0 < (size incl - 1).+1 | (i0
                                    != 
                                   (@inord  (size incl - 1) (index i incl))) &&
                                    ~~
                                    (i0 <
                                    (@inord  (size incl - 1) (index i incl)))%N)
             (x_general mal init A (t_eps + j) (nth i incl i0) *
              w (t_eps + j) (i, nth i incl i0))%Re)%Ri))%Re.
        ++ apply Rplus_le_compat_l. rewrite -RplusE. apply Rplus_le_compat_r.
           rewrite /incl. by apply x_left_ineq_1. 
        ++ apply Rle_trans with
            (M_general mal init A (t_eps + j) * w (t_eps + j) (i, i) +
             ((\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                               (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                  w (t_eps + j) (i, nth i incl i0)) *
              (A_M - eps_j j eps_0 eps a) +
              (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                              ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                  w (t_eps + j) (i, nth i incl i0)) * M_general mal init A (t_eps+j)))%Re.
            * apply Rplus_le_compat_l. apply Rplus_le_compat_l.
              rewrite /incl. by apply (@x_right_ineq_1 i a A_M t_eps j eps eps_0). 
            * assert ((M_general mal init A (t_eps + j) * w (t_eps + j) (i, i) +
                       ((\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0)) *
                        (A_M - eps_j j eps_0 eps a) +
                        (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0)) * M_general mal init A (t_eps + j)))%Re = 
                       ((w (t_eps + j) (i, i) + (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0))) * M_general mal init A (t_eps+j) + 
                        (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0)) *
                        (A_M - eps_j j eps_0 eps a))%Re).
              { nra. } rewrite H17.  clear H17.
              assert (( A_M - (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re = 
                      ((1-a)* (A_M + eps) + a * (A_M - eps_j j eps_0 eps a))%Re).
              { nra. } rewrite H17.
              rewrite (@big_cond_simpl_gt i incl (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
              rewrite (@big_cond_simpl_lt i incl (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
              assert ((w (t_eps + j) (i, i) +
                        \sum_(i0 < (size incl - 1).+1 | 
                        ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                           w (t_eps + j) (i, nth i incl i0))%Re =
                      (1 - (\sum_(i0 < (size incl - 1).+1 | 
                            (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                               w (t_eps + j) (i, nth i incl i0)))%Re).
              { assert ((w (t_eps + j) (i, i) +
                         \sum_(i0 < (size incl - 1).+1 | 
                         ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                            w (t_eps + j) (i, nth i incl i0))%Re =
                        (1 -
                         \sum_(i0 < (size incl - 1).+1 | 
                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0))%Re <-> 
                        (w (t_eps + j) (i, i) +
                         \sum_(i0 < (size incl - 1).+1 | 
                         ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                            w (t_eps + j) (i, nth i incl i0) + \sum_(i0 < (size incl - 1).+1 | 
                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0))%Re = 1%Re). { nra. }
                rewrite H18. clear H18. rewrite sum_f_R0_big_equiv in H10. rewrite -H10.
                rewrite [in RHS](bigD1 (inord (index i incl))) //=.
                rewrite inordK.
                + rewrite nth_index.
                  - rewrite Rplus_assoc. rewrite -[in RHS]RplusE.
                    apply Rplus_eq_compat_l. 
                    rewrite [in RHS](@big_nat_split i incl 
                        (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
                    rewrite (@big_cond_simpl_gt i incl 
                        (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
                    rewrite (@big_cond_simpl_lt i incl 
                        (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
                    rewrite inordK.
                    * by rewrite -RplusE Rplus_comm. 
                    * apply ltn_leq_trans with (size incl). 
                      ++ rewrite index_mem. apply i_in_incl_general.
                      ++ rewrite subn1. rewrite prednK.
                         + by [].
                         + apply size_incl_not_0_general.
                    * apply i_in_incl_general.
                + apply ltn_leq_trans with (size incl). 
                  - rewrite index_mem. apply i_in_incl_general.
                  - rewrite subn1. rewrite prednK.
                    * by [].
                    * apply size_incl_not_0_general.
              } rewrite H18.
              remember (\sum_(i0 < (size incl - 1).+1 | 
                          (i0 < inord (index i incl))%N)
                             w (t_eps + j) (i, nth i incl i0)) as w_il.
              assert ((M_general mal init A (t_eps+j)%N < A_M + eps)%Re). 
              { apply H11. apply /leP. apply leq_addr. }
              apply Rle_trans with ((1 - a) * M_general mal init A (t_eps + j)%N +
                                      a * (A_M - eps_j j eps_0 eps a))%Re.
              - assert (((1 - w_il) * M_general mal init A (t_eps + j) +
                              w_il * (A_M - eps_j j eps_0 eps a))%Re = 
                        (M_general mal init A (t_eps + j) - w_il * ( M_general mal init A (t_eps + j) - (A_M - eps_j j eps_0 eps a)))%Re).
                { nra. } rewrite H20.
                assert (((1 - a) * M_general mal init A (t_eps + j) +
                            a * (A_M - eps_j j eps_0 eps a))%Re = 
                         (M_general mal init A (t_eps + j) - a * (M_general mal init A (t_eps + j) - (A_M - eps_j j eps_0 eps a)))%Re).
                { nra. } rewrite H21.
                apply Rplus_le_compat_l, Ropp_ge_le_contravar.
                apply Rmult_ge_compat_r.
                * apply Rge_minus, Rle_ge. apply Rle_trans with A_M.
                  ++ assert ((0 < eps_j j eps_0 eps a)%Re).
                     { by apply eps_j_gt_0 with N. } nra.
                  ++ by apply M_A_M_lower_bound.
                * apply Rle_ge. rewrite Heqw_il. by apply w_ge_a_1.
              - apply  Rplus_le_compat_r, Rmult_le_compat_l.
                + nra. 
                + by apply Rlt_le.
    - apply i_in_incl_general.
  + rewrite subn1. rewrite prednK.
    - rewrite index_mem.  apply i_in_incl_general.
    - rewrite -has_predT. apply /hasP. exists i.
      * apply i_in_incl_general.
      * by [].
Qed.


Lemma and_2_conv: forall (P Q:bool),
  P && Q -> P /\ Q.
Proof.
intros. destruct P.
+ simpl. by destruct Q.
+ by simpl in H.
Qed.

Lemma x_in_incl_not_X_M (i:D) (a A_M:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool): 
  forall (k:D),
  (k \in (in_neighbor i :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j)%N mal init A)) ->
    (x_general mal init A (t_eps+j)%N k <= (A_M - eps_j j eps_0 eps a))%Re. 
Proof.
intros. rewrite in_setD in H. apply and_2_conv in H.
destruct H.
rewrite inE in H.
destruct ( Rgt_dec (x_general mal init A (t_eps + j) k)
                (A_M - eps_j j eps_0 eps a)).
+ by simpl in H.
+ simpl in H. by apply Rnot_gt_le in n.
Qed.


Lemma or_2_conv: forall (P Q:bool), P || Q -> P \/ Q.
Proof.
intros. destruct P.
+ by left.
+ destruct Q.
  - by right.
  - by simpl in H.
Qed.


Lemma in_neighbor_subset_incl (i:D) (a A_M:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D ->R) (init : D -> R) (A: D -> bool):
  i \in Normal_general A ->
  (x_general mal init A (t_eps + j) i > A_M - eps_j j eps_0 eps a)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in 
  {subset (in_neighbor i  :\: 
                X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) <= 
     [set x | x \in incl] :|: R_i_less_than_general mal init A i (t_eps+j)%N }.
Proof.
intros. rewrite /sub_mem //=. move=> k.
intros. rewrite inE in H1. apply and_2_conv in H1.
destruct H1. rewrite inE in H1. rewrite in_setU. apply /orP.
rewrite inE. 
destruct (Rgt_dec (x_general mal init A (t_eps + j) k) (A_M - eps_j j eps_0 eps a)).
+ by simpl in H1.
+ simpl in H1. 
  assert ((F <= index k (inclusive_neighbor_list i))%N \/ (index k (inclusive_neighbor_list i) <=F)%N).
  { apply /orP. apply leq_total. }
  destruct H3.
  - left.
    rewrite /incl /incl_neigh_minus_extremes /remove_extremes //=.
    rewrite mem_filter. apply /andP. split.
    * apply /andP. split.
      ++ apply /orP. by right.
      ++ apply /orP. left.
         destruct (Rle_dec (x_general mal init A (t_eps + j) k) (x_general mal init A (t_eps + j) i)).
         - by simpl.
         - simpl.
           assert ((x_general mal init A (t_eps + j) k <= x_general mal init A (t_eps + j) i)%Re).
           { apply Rle_trans with (A_M - eps_j j eps_0 eps a)%Re.
             + by apply Rnot_gt_le in n.
             + by apply Rlt_le.
           } contradiction.
    * rewrite /inclusive_neighbor_list /inclusive_neigh.
      assert (k \in (in_neighbor i :|: [set i])). 
      { rewrite in_setU. apply /orP. by left. }
      assert ([set x | x \in enum (in_neighbor i :|: [set i])] = (in_neighbor i :|: [set i])).
      { apply set_enum. } rewrite -H5 in H4.
      by rewrite inE in H4.
  - rewrite leq_eqVlt in H3.
    assert ((index k (inclusive_neighbor_list i) == F)
              \/ (index k (inclusive_neighbor_list i) < F)%N).
    { by apply /orP. } destruct H4. 
    * assert (index k (inclusive_neighbor_list i) = F).
      { by apply /eqP. }
      left. rewrite /incl /incl_neigh_minus_extremes /remove_extremes //=.
      rewrite mem_filter. apply /andP. split.
      ++ apply /andP. split.
         - apply /orP. right. by rewrite H5.
         - apply /orP. left.
           destruct (Rle_dec (x_general mal init A (t_eps + j) k) (x_general mal init A (t_eps + j) i)).
           * by simpl.
           * simpl.
             assert ((x_general mal init A (t_eps + j) k <= x_general mal init A (t_eps + j) i)%Re).
             { apply Rle_trans with (A_M - eps_j j eps_0 eps a)%Re.
               + by apply Rnot_gt_le in n.
               + by apply Rlt_le.
             } contradiction.
      ++ rewrite /inclusive_neighbor_list /inclusive_neigh.
          assert (k \in (in_neighbor i :|: [set i])). 
          { rewrite in_setU. apply /orP. by left. }
          assert ([set x | x \in enum (in_neighbor i :|: [set i])] = (in_neighbor i :|: [set i])).
          { apply set_enum. } rewrite -H7 in H6.
          by rewrite inE in H6.
    * right. rewrite inE. apply /andP. split.
      ++ apply /andP. split.
         - destruct (Rlt_dec (x_general mal init A (t_eps + j) k) (x_general mal init A (t_eps + j) i)).
           * by simpl.
           * simpl.
             assert ((x_general mal init A (t_eps + j) k < x_general mal init A (t_eps + j) i)%Re).
             { apply Rle_lt_trans with (A_M - eps_j j eps_0 eps a)%Re.
               + by apply Rnot_gt_le in n.
               + by [].
             } contradiction.
         - by [].
      ++ rewrite /inclusive_neighbor_list /inclusive_neigh.
          assert (k \in (in_neighbor i :|: [set i])). 
          { rewrite in_setU. apply /orP. by left. }
          assert ([set x | x \in enum (in_neighbor i :|: [set i])] = (in_neighbor i :|: [set i])).
          { apply set_enum. } rewrite -H6 in H5.
           by rewrite inE in H5.
Qed.

Lemma s_subset_incl (i:D) (a A_M:R) (t_eps j:nat) (eps eps_0: posreal) (s: seq D)
  (mal : nat -> D-> R) (init : D -> R) (A: D -> bool): 
  i \in Normal_general A ->
  (x_general mal init A (t_eps + j) i > A_M - eps_j j eps_0 eps a)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in 
  {subset s <= in_neighbor i  :\: 
                X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A } ->
  {subset s <= [set x | x \in incl] :|: R_i_less_than_general mal init A i (t_eps+j)%N}.
Proof.
intros.
assert ({subset [set x | x \in s] <= [set x | x \in incl] :|: R_i_less_than_general mal init A i (t_eps+j)%N}).
{ apply /subsetP.
  apply (@subset_trans D [set x | x \in s] 
   (in_neighbor i  :\: 
                  X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A)
    ([set x | x \in incl] :|: R_i_less_than_general mal init A i (t_eps+j)%N)). 
  + apply /subsetP. rewrite /sub_mem //=. intros.
    rewrite inE in H2. rewrite /sub_mem in H1. 
    by specialize (H1 x H2).
  + rewrite /incl. apply /subsetP. by apply in_neighbor_subset_incl.
} rewrite /sub_mem //=. intros. rewrite /sub_mem in H2.
specialize (H2 x). rewrite inE in H2. by specialize (H2 H3).
Qed.




Lemma P_or_Q_exchange: forall (P Q: bool), 
  P || Q -> Q || P.
Proof.
intros. destruct P.
+ by destruct Q.
+ destruct Q.
  - by simpl.
  - by simpl in H.
Qed.


Lemma bound_intersect: forall (A B: {set D}), 
  (#|A :&: B| <= #|B|)%N.
Proof.
intros. apply subset_leq_card .
apply /subsetP. rewrite /sub_mem.
intros. rewrite in_setI in H.
assert ((x \in A) /\ (x \in B)).
{ by apply /andP. } by destruct H0.
Qed.


Lemma exists_in_intersection: forall (A B: {set D}) (s: seq D) (F:nat),
  #|s| = (F+1)%N ->
  (#|B| <= F)%N ->
  {subset s <= A :|: B} ->
  exists x:D, x \in [set x | x \in s] :&: A.
Proof.
intros.
assert (s \subset A :|: B).
{ by apply /subsetP. }
assert ([set x | x \in s] \subset B :|: A).
{ apply /subsetP. rewrite /sub_mem //=. 
  intros. rewrite inE in H3. rewrite /sub_mem in H1.
  assert (x \in A :|: B <-> x \in B :|: A).
  { split.
    + intros. rewrite in_setU.  rewrite in_setU in H4. by apply P_or_Q_exchange.
    + intros. rewrite in_setU.  rewrite in_setU in H4. by apply P_or_Q_exchange.
  } rewrite -H4. by apply H1.
} rewrite -subDset in H3.
assert (exists x:D, x \in finset (in_mem^~ (mem s)) :\: B).
{ apply /card_gt0P. rewrite cardsD. rewrite cardsE. rewrite subn_gt0. 
  apply leq_ltn_trans with F.
  + apply leq_trans with #|B|.
    - apply bound_intersect.
    - by [].
  + rewrite H. rewrite addn1. apply ltnSn.
} destruct H4 as [k H4].
assert ({subset finset (in_mem^~ (mem s)) :\: B <= A }).
{ by apply /subsetP. } rewrite /sub_mem in H5.
specialize (H5 k H4).
exists k. rewrite in_setI. rewrite inE.
rewrite in_setD in H4. rewrite inE in H4.
assert ((k \notin B) /\ (k \in s)).
{ by apply /andP. } destruct H6.
by apply /andP.
Qed.



Lemma in_intersect_implies_in_s:  forall (A B: {set D}) (s: seq D) (F:nat),
  (exists x:D, x \in [set x | x \in s] :&: A) ->
  exists x:D, x \in s.
Proof.
intros. destruct H. exists x. rewrite in_setI in H.
assert ((x \in finset (in_mem^~ (mem s))) /\ (x \in A)).
{ by apply /andP. } destruct H0. by rewrite inE in H0.
Qed.



Lemma k_in_incl_bounded (i:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init ->
  is_lim_seq [eta M_general mal init A] A_M -> 
  (0<N)%N-> (j<=N)%N ->
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (F + 1 <= #|in_neighbor i :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A|)%N ->
  (x_general mal init A (t_eps + j) i > A_M - eps_j j eps_0 eps a)%Re ->
  (forall k: 'I_(size incl - 1).+1,
               (x_general mal init A (t_eps + j) (nth i incl k) <= M_general mal init A (t_eps + j))%Re).
Proof.
intros.
assert ((k <= @inord (size incl-1) (index i incl))%N \/
        (k >= @inord (size incl-1) (index i incl))%N).
{ apply /orP. apply leq_total. }
destruct H13.
+ rewrite leq_eqVlt in H13.
  assert ( (k == @inord (size incl -1) (index i incl))
             \/ (k < @inord (size incl -1) (index i incl))%N).
  { by apply /orP. } destruct H14.
  - assert (k = inord (index i incl)).
    { by apply /eqP. } rewrite H15.
    rewrite inordK.
    * rewrite nth_index.
      ++ by apply x_bound.
      ++ apply i_in_incl_general.
    * rewrite subn1 prednK.
      ++ rewrite index_mem. apply i_in_incl_general.
      ++ apply size_incl_not_0_general.
  - apply Rle_trans with  (x_general mal init A (t_eps + j) (nth i incl (@inord (size incl -1) (index i incl))))%Re.
    * rewrite inordK.
      ++ rewrite nth_index.
         - assert (sorted_Dseq_general incl).
           { apply lemma_1.incl_sorted_general. } rewrite /sorted_Dseq_general in H15.
           apply H15.
           * apply mem_nth. apply ltn_leq_trans with (size incl - 1).+1.
             ++ apply ltn_ord.
             ++ rewrite subn1. rewrite ltn_predL. apply size_incl_not_0_general.
           * apply i_in_incl_general.
           * rewrite index_uniq.
             ++ rewrite inordK in H14.
                - by [].
                - rewrite subn1 prednK.
                  * rewrite index_mem. apply i_in_incl_general.
                  * apply size_incl_not_0_general.
             ++ apply ltn_leq_trans with (size incl - 1).+1.
                - apply ltn_ord.
                - rewrite subn1. rewrite ltn_predL. apply size_incl_not_0_general.
             ++ apply incl_uniq_general.
         - apply i_in_incl_general.
      ++ rewrite subn1 prednK. rewrite index_mem. apply i_in_incl_general. apply size_incl_not_0_general.
    * rewrite inordK.
      ++ rewrite nth_index.
         - by apply x_bound.
         - apply i_in_incl_general.
      ++ rewrite subn1 prednK. rewrite index_mem. apply i_in_incl_general. apply size_incl_not_0_general.
+ assert ((nth i incl k) \in Normal_general A \/ (nth i incl k) \in Adversary_general A).
  { apply normal_or_adversary. }
  destruct H14.
  - by apply x_bound.
  - assert ((#|R_i_greater_than_general mal init A i (t_eps + j)%N| <= F)%N).
    { apply R_i_gt_bounded_general . } rewrite leq_eqVlt in H15.
    assert ( (#|R_i_greater_than_general mal init A i (t_eps + j)| == F)
              \/ (#|R_i_greater_than_general mal init A i (t_eps + j)| < F)%N).
    { by apply /orP. } destruct H16.
    * assert(R_i_greater_than_general mal init A i (t_eps + j) == Adversary_general A \/
                  R_i_greater_than_general mal init A i (t_eps + j) != Adversary_general A).
      { apply /orP.
        by destruct (R_i_greater_than_general mal init A i (t_eps + j) == Adversary_general A).
      } destruct H17.
      ++ assert (R_i_greater_than_general mal init A i (t_eps + j) == Adversary_general A ->
                  nth i incl k \notin Adversary_general A).
         { by apply incl_does_not_contain_adversary. } specialize (H18 H17). 
         assert (~ (nth i incl k \in Adversary_general A)).
         { by apply /negP. } contradiction.
      ++ assert (exists k:D, k \in (Normal_general A :&: (R_i_greater_than_general mal init A  i (t_eps+j)%N))).
        { by apply exists_an_elem_in_out_set with k.  } destruct H18 as [p H18]. rewrite in_setI in H18.
        assert ((p \in Normal_general A) /\
                     (p \in R_i_greater_than_general mal init A i (t_eps + j))).
        { by apply /andP. } destruct H19.
        apply Rle_trans with (x_general mal init A (t_eps + j) p).
        * apply R_i_gt_val_rel with i.
          ++ rewrite -/incl. apply mem_nth.
             apply ltn_leq_trans with (size incl - 1).+1.
             + by apply ltn_ord.
             + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
               rewrite ltn_subrL. apply /andP. split.
               - by [].
               - apply H21.
          ++ apply H20.
        * by apply x_bound.
    * (** The last node has the value same as x_i(t) and since i is Normal,
        x_i <= M **)
      apply Rle_trans with (x_general mal init A (t_eps + j)%N (last (head i incl) (behead incl))).
      - apply last_incl_is_max_general. rewrite -/incl. apply mem_nth.
        apply ltn_leq_trans with (size incl - 1).+1.
        + by apply ltn_ord.
        + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
          rewrite ltn_subrL. apply /andP. split.
          - by [].
          - apply H17.
      - assert (((x_general mal init A (t_eps + j) (last (head i incl ) (behead incl ))) = (x_general mal init A (t_eps + j) i))%Re).
        { by apply card_R_i_gt_lt_F_exchange_last_general. } rewrite H17.
        by apply x_bound.
Qed.


Lemma x_not_k_bound (i k:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal) (s: seq D)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init ->
  is_lim_seq [eta M_general mal init A] A_M -> 
  (0<N)%N-> (j<=N)%N ->
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (F + 1 <= #|in_neighbor i :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A|)%N ->
  (x_general mal init A (t_eps + j) i > A_M - eps_j j eps_0 eps a)%Re ->
  {subset s
           <= in_neighbor i
              :\: X_M_t_e_i (eps_j j eps_0 eps a)
                    A_M (t_eps + j) mal init A} ->
  k \in incl ->
  k \in s ->
  (\sum_(i0 < (size incl - 1).+1 | 
 i0 != inord (index k incl))
    (x_general mal init A (t_eps + j) (nth i incl i0) *
     w (t_eps + j) (i, nth i incl i0))%Re <=
 (\sum_(i0 < (size incl - 1).+1 | 
  i0 != inord (index k incl))
     w (t_eps + j) (i, nth i incl i0)) *
 M_general mal init A (t_eps + j))%Re.
Proof.
intros.
assert (((\sum_(i0 < (size incl - 1).+1 | 
          i0 != inord (index k incl))
             w (t_eps + j) (i, nth i incl i0)) *
         M_general mal init A (t_eps + j))%Re = 
       \sum_(i0 < (size incl - 1).+1 | 
          i0 != inord (index k incl))
             (w (t_eps + j) (i, nth i incl i0) * M_general mal init A (t_eps+j))%Re).
{ by rewrite big_distrl //=. } rewrite H16. apply /RleP.
apply big_sum_ge_ex_abstract. intros.
rewrite Rmult_comm. apply Rmult_le_compat_l.
+ apply Rle_trans with a.
  - nra.
  - apply H8. apply mem_nth. 
    apply ltn_leq_trans with (size incl - 1).+1 .
    * apply ltn_ord.
    * rewrite subn1. rewrite ltn_predL. apply size_incl_not_0_general.
+ assert (i0 != @inord (size incl -1) (index k incl) :> nat).
  { by []. } rewrite inordK in H18.
  - assert (forall k: 'I_(size incl - 1).+1,
               (x_general mal init A (t_eps + j) (nth i incl k) <= M_general mal init A (t_eps + j))%Re).
    { by apply k_in_incl_bounded with a A_m A_M N eps eps_0.  } apply H19.
  - rewrite subn1 prednK.
    * by rewrite index_mem.
    * apply size_incl_not_0_general.
Qed.
  
Lemma x_val_decreases_2 (i:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta M_general mal init A] A_M -> 
  (0<N)%N-> (j<=N)%N ->
   i \in Normal_general  A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (F + 1 <= #|in_neighbor i :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A|)%N ->
  (x_general mal init A (t_eps + j) i > A_M - eps_j j eps_0 eps a)%Re ->
  (x_general mal init A (t_eps + j.+1) i <=  A_M - eps_j j.+1 eps_0 eps a)%Re.
Proof.
intros.  simpl. 
assert ((t_eps + j.+1)%N = (t_eps + j).+1).
{ by rewrite -addn1 addnA addn1. } rewrite H14.
simpl.
assert (A i = false).
{ rewrite !inE in H5. simpl in H5. 
  assert ( (A i != true) /\ true).
  { by apply /andP. } destruct H15. 
  by destruct (A i).
} rewrite H15 //=.
rewrite sum_f_R0_big_equiv. rewrite -/incl.
assert (exists s, [/\ uniq s, size s = (F+1)%N & 
              {subset s <= (in_neighbor i :\: X_M_t_e_i  (eps_j j eps_0 eps a) A_M (t_eps+j)%N mal init A)}]).
{ by apply /card_geqP. } destruct H16 as [s H16].
destruct H16.
assert (exists k:D, k \in [set x | x \in s] :&: [set x | x \in incl]).
{ apply exists_in_intersection with (R_i_less_than_general mal init A i (t_eps+j)%N ) F.
  + assert (#|s| = size s). { by apply /card_uniqP. }
    by rewrite H19.
  + apply R_i_lt_bounded_general.
  + by apply s_subset_incl with a A_M eps eps_0.
} destruct H19 as [k H19].
rewrite in_setI !inE in H19.
    assert ( (k \in s) /\ (k \in incl)).
    { by apply /andP. } destruct H20.
rewrite (bigD1 (inord (index k incl))) //=.
rewrite inordK.
+ rewrite nth_index.
  - rewrite -RplusE.
    assert ((\sum_(i0 < (size incl - 1).+1 | 
             i0 != inord (index k incl))
                (x_general mal init A (t_eps + j) (nth i incl i0) *
                 w (t_eps + j) (i, nth i incl i0))%Re <=
            ((\sum_(i0 < (size incl - 1).+1 | 
                i0 != inord (index k incl))  w (t_eps + j) (i, nth i incl i0)) *
             M_general mal init A (t_eps+j))%Re)%Re).
    { by apply x_not_k_bound with a A_m A_M N eps eps_0 s. }
   apply Rle_trans with 
    (x_general mal init A (t_eps + j) k * w (t_eps + j) (i, k) + 
      ((\sum_(i0 < (size incl - 1).+1 | 
        i0 != inord (index k incl))
           w (t_eps + j) (i, nth i incl i0)) *
       M_general mal init A (t_eps + j))%Re)%Re.
   * by apply Rplus_le_compat_l.
   * apply Rle_trans with 
      ( (w (t_eps + j) (i, k) * (A_M - eps_j j eps_0 eps a))%Re+
         (\sum_(i0 < (size incl - 1).+1 | 
          i0 != inord (index k incl))
             w (t_eps + j) (i, nth i incl i0)) *
         M_general mal init A (t_eps + j))%Re.
     ++ apply Rplus_le_compat_r. rewrite Rmult_comm. apply Rmult_le_compat_l.
        - apply Rle_trans with a.
          * nra.
          * by apply H9.
        - apply x_in_incl_not_X_M with i. rewrite /sub_mem in H18.
          by specialize (H18 k H20).
     ++ assert (( A_M - (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re = 
                      ((1-a)* (A_M + eps) + a * (A_M - eps_j j eps_0 eps a))%Re).
        { nra. } rewrite H23.
        assert (\sum_(i0 < (size incl - 1).+1 | 
                  i0 != inord (index k incl))
                     w (t_eps + j) (i, nth i incl i0) = 
                (1 - w (t_eps + j) (i, k))%Re).
        { assert (\sum_(i0 < (size incl - 1).+1 | i0
                                != 
                                inord
                                (index k incl))
                       w (t_eps + j) (i, nth i incl i0) =
                    (1 - w (t_eps + j) (i, k))%Re <->
                  (w (t_eps + j) (i, k) + 
                    \sum_(i0 < (size incl - 1).+1 | i0
                                != 
                                inord
                                (index k incl))
                       w (t_eps + j) (i, nth i incl i0))%Re = 1%Re).
          { nra. } rewrite H24. clear H24.
          rewrite sum_f_R0_big_equiv in H10. rewrite -H10.
          rewrite [in RHS](bigD1 (inord (index k incl))) //=.
          rewrite inordK.
          + by rewrite nth_index.
          + rewrite subn1 prednK. rewrite index_mem.
            - by [].
            - apply size_incl_not_0_general.
        } rewrite H24. clear H24.
        remember (w (t_eps + j) (i, k)) as w_ik.
        assert ((M_general mal init A (t_eps+j)%N < A_M + eps)%Re). 
        { apply H11. apply /leP. apply leq_addr. }
        apply Rle_trans with ((1 - a) * M_general mal init A (t_eps + j)%N +
                                      a * (A_M - eps_j j eps_0 eps a))%Re.
        - assert ((w_ik * (A_M - eps_j j eps_0 eps a) +
                    (1 - w_ik) * M_general mal init A (t_eps + j))%Re = 
                        (M_general mal init A (t_eps + j) - w_ik * ( M_general mal init A (t_eps + j) - (A_M - eps_j j eps_0 eps a)))%Re).
          { nra. } rewrite H25.
          assert (((1 - a) * M_general mal init A (t_eps + j) +
                            a * (A_M - eps_j j eps_0 eps a))%Re = 
                         (M_general mal init A (t_eps + j) - a * (M_general mal init A (t_eps + j) - (A_M - eps_j j eps_0 eps a)))%Re).
          { nra. } rewrite H26.
          apply Rplus_le_compat_l, Ropp_ge_le_contravar.
          apply Rmult_ge_compat_r.
          * apply Rge_minus, Rle_ge. apply Rle_trans with A_M.
            ++ assert ((0 < eps_j j eps_0 eps a)%Re).
               { by apply eps_j_gt_0 with N. } nra.
            ++ by apply M_A_M_lower_bound. 
          * apply Rle_ge. rewrite Heqw_ik. apply H9.
            by []. 
        - apply  Rplus_le_compat_r, Rmult_le_compat_l.
          + nra. 
          + by apply Rlt_le.
  - by [].
+ rewrite subn1. rewrite prednK.
  - by rewrite index_mem. 
  - apply size_incl_not_0_general.
Qed.



Lemma exists_an_elem_in_out_set_R_lt (i:D) (t:nat)
  (mal : nat -> D -> R) (init: D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  R_i_less_than_general mal init A i t != Adversary_general A -> 
  #|R_i_less_than_general mal init A i t| == F ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
  forall i0 : 'I_(size incl - 1).+1, 
  nth i incl i0 \in (Adversary_general A) ->
  exists k:D, k \in (Normal_general A :&: (R_i_less_than_general mal init A i t)).
Proof.
intros.
assert (exists (j:D), (j \in Normal_general A) /\ (j \in R_i_less_than_general mal init A i t)).
{ by apply exists_normal_node_in_R_i_lt_general. }
destruct H3 as [j H3]. exists j.
rewrite in_setI. by apply /andP.
Qed.


Lemma not_in_R_i_less_than (i j:D) (t:nat)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
    (j \in incl \/ j \in R_i_greater_than_general mal init A i t) ->
      (j \notin R_i_less_than_general mal init A i t).
Proof.
intros. destruct H.
+ rewrite inE. rewrite /incl /incl_neigh_minus_extremes /remove_extremes in H.
  rewrite mem_filter in H. apply and_conv in H.
  destruct H. destruct H0.
  apply /nandP. left.
  apply /nandP. 
  assert (Rge_dec (x_general mal init A t j) (x_general mal init A t i)
             \/ (F <= index j (inclusive_neighbor_list i))%N).
  { by apply /orP. } destruct H2.
  - left. destruct (Rge_dec (x_general mal init A t j) (x_general mal init A t i)).
    * simpl in H2. 
      destruct (Rlt_dec (x_general mal init A t j) (x_general mal init A t i)).
      ++ simpl. apply Rlt_not_ge in r0. contradiction.
      ++ by simpl.
    * simpl in H2. by [].
  - right. by rewrite -leqNgt.
+ rewrite inE. rewrite inE in H. apply and_conv in H.
  destruct H. destruct H0. apply /nandP. left.
  apply /nandP. left.
  destruct (Rgt_dec (x_general mal init A t j) (x_general mal init A t i)).
  - destruct (Rlt_dec (x_general mal init A t j) (x_general mal init A t i)).
    * simpl. apply Rgt_asym in r0. contradiction.
    * by simpl in H.
  - by simpl in H.
Qed.


Lemma incl_R_lt_does_not_contain_adversary (i:D) (t:nat)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
  forall (i0 : 'I_(size incl - 1).+1), 
  R_i_less_than_general mal init A i t == Adversary_general A ->
                  nth i incl i0 \notin Adversary_general A.
Proof.
intros. rewrite -Normal_adversary_disjoint_general.
rewrite Normal_not_adversary.
assert (R_i_less_than_general mal init A i t = Adversary_general A).
{ by apply /eqP. } rewrite -H0. 
rewrite in_setC. 
apply (@not_in_R_i_less_than  i (nth i incl i0) t).
left. rewrite -/incl. 
apply mem_nth.
apply ltn_leq_trans with (size incl - 1).+1.
- by apply ltn_ord.
- assert ((0< size incl)%N). { apply size_incl_not_0_general. }
  rewrite ltn_subrL. apply /andP. split.
  * by [].
  * apply H1.
Qed.


Lemma R_i_lt_val_rel (i:D) (t:nat)
  (mal : nat -> D ->R) (init : D -> R) (A: D -> bool) :
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A) t in
  forall j k:D, 
    k \in incl -> 
     j \in (R_i_less_than_general mal init A i t) ->
      (x_general mal init A t j <= x_general mal init A t k)%Re.
Proof.
intros. rewrite /R_i_less_than_general in H0.
rewrite inE in H0. apply and_conv in H0. destruct H0.
destruct H1.
destruct (Rlt_dec (x_general mal init A t j) (x_general mal init A t i)).
+ simpl in H0.
  rewrite /incl / incl_neigh_minus_extremes /remove_extremes in H.
  rewrite mem_filter in H. apply and_conv in H. destruct H.
  destruct H3.
  assert (Rge_dec (x_general mal init A t k) (x_general mal init A t i)
             \/ (F <= index k (inclusive_neighbor_list i))%N).
  { by apply /orP. } destruct H5.
  - destruct (Rge_dec (x_general mal init A t k) (x_general mal init A t i)).
    * simpl in H5. apply Rle_trans with (x_general mal init A t i).
      ++ by apply Rlt_le.
      ++ apply Rge_le, r0.
    * by simpl in H5.
  - assert (sorted_Dseq_general (inclusive_neighbor_list i)).
    { by apply lemma_1.inclusive_neighbors_sorted_general. } rewrite /sorted_Dseq_general in H6.
    apply H6.
    - apply H2.
    - apply H4.
    - by apply ltn_leq_trans with F.
+ by simpl in H0.
Qed.

Lemma x_left_ineq_2 (i:D) (a A_m:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A : D -> bool):
  F_total_malicious_general mal init A ->
   i \in Normal_general A -> (0 < a)%Re -> (a < 1)%Re ->
  (*(x (t_eps + j) i >= A_m + eps_j j eps_0 eps a)%Re -> *)
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
        (i0 < (@inord  (size incl - 1) (index i incl)))%N)
          (x_general mal init A (t_eps + j) (nth i incl i0) *
           w (t_eps + j) (i, nth i incl i0))%Re >=
  (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
    (i0 < (@inord  (size incl - 1) (index i incl)))%N)
       w (t_eps + j) (i, nth i incl i0)) * m_general mal init A (t_eps + j))%Re.
Proof.
intros. rewrite (@big_cond_simpl_lt i incl (fun i0:nat => (x_general mal init A (t_eps + j) (nth i incl i0) *
                    w (t_eps + j) (i, nth i incl i0))%Re)).
rewrite (@big_cond_simpl_lt i incl (fun i0:nat =>  w (t_eps + j) (i, nth i incl i0))).
apply Rle_ge. apply /RleP.
assert (((\sum_(i0 < (size incl - 1).+1 | 
              (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                 w (t_eps + j) (i, nth i incl i0)) *
             m_general mal init A (t_eps + j))%Re = 
          \sum_(i0 < (size incl - 1).+1 | 
             (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                 ((w (t_eps + j) (i, nth i incl i0)) *
             m_general mal init A (t_eps + j))%Re).
{ by rewrite big_distrl //=. } rewrite H4.
apply big_sum_ge_ex_abstract.
intros. rewrite Rmult_comm. apply Rmult_le_compat_r.
+ apply Rle_trans with a.
  - by apply Rlt_le.
  - apply H3. apply mem_nth.
    apply ltn_leq_trans with (size incl - 1).+1.
    ++ by apply ltn_ord.
    ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
       rewrite ltn_subrL. apply /andP. split.
       - by [].
       - apply H6.
+ assert ((nth i incl i0) \in Normal_general A \/ (nth i incl i0) \in Adversary_general A).
  { apply normal_or_adversary. }
  destruct H6.
  - by apply x_bound.
  - assert ((#|R_i_less_than_general mal init A i (t_eps + j)%N| <= F)%N).
    { apply R_i_lt_bounded_general. } rewrite leq_eqVlt in H7.
    assert ( (#|R_i_less_than_general mal init A i (t_eps + j)| == F)
              \/ (#|R_i_less_than_general mal init A i (t_eps + j)| < F)%N).
    { by apply /orP. } destruct H8.
    * assert(R_i_less_than_general mal init A i (t_eps + j) == Adversary_general A \/
                  R_i_less_than_general mal init A i (t_eps + j) != Adversary_general A).
      { apply /orP.
        by destruct (R_i_less_than_general mal init A i (t_eps + j) == Adversary_general A).
      } destruct H9.
      ++ assert (R_i_less_than_general mal init A i (t_eps + j) == Adversary_general A ->
                  nth i incl i0 \notin Adversary_general A).
         { by apply incl_R_lt_does_not_contain_adversary. } specialize (H10 H9). 
         assert (~ (nth i incl i0 \in Adversary_general A)).
         { by apply /negP. } contradiction.
      ++ assert (exists k:D, k \in (Normal_general A :&: (R_i_less_than_general mal init A  i (t_eps+j)%N))).
        { by apply exists_an_elem_in_out_set_R_lt with i0.  } destruct H10 as [k H10]. rewrite in_setI in H10.
        assert ((k \in Normal_general A) /\
                     (k \in R_i_less_than_general mal init A i (t_eps + j))).
        { by apply /andP. } destruct H11.
        apply Rle_trans with (x_general mal init A (t_eps + j) k).
        * by apply x_bound.
        * apply R_i_lt_val_rel with i.
          ++ rewrite -/incl. apply mem_nth.
             apply ltn_leq_trans with (size incl - 1).+1.
             + by apply ltn_ord.
             + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
               rewrite ltn_subrL. apply /andP. split.
               - by [].
               - apply H13.
          ++ apply H12.
    * (** The last node has the value same as x_i(t) and since i is Normal,
        x_i <= M **)
      apply Rle_trans with (x_general mal init A (t_eps + j)%N (nth i (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)) 0)).
      - assert (((x_general mal init A (t_eps+j) (nth i (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)) 0)) = (x_general mal init A (t_eps + j) i))%Re).
        { by apply  card_R_i_lt_lt_F_exchange_first_general. } rewrite H9.
        by apply x_bound.
      - apply first_incl_is_min_general. rewrite -/incl. apply mem_nth.
        apply ltn_leq_trans with (size incl - 1).+1.
        + by apply ltn_ord.
        + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
          rewrite ltn_subrL. apply /andP. split.
          - by [].
          - apply H9.
Qed.


Lemma x_right_ineq_2 (i:D) (a A_m:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
   i \in Normal_general A -> (0 < a)%Re -> (a < 1)%Re ->
  (x_general mal init A (t_eps + j) i >= A_m + eps_j j eps_0 eps a)%Re  ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  (\sum_(i0 < (size incl - 1).+1 | (i0 !=(@inord  (size incl - 1) (index i incl))) &&
                                 ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
    (x_general mal init A (t_eps + j) (nth i incl i0) *
     w (t_eps + j) (i, nth i incl i0))%Re >=
 (\sum_(i0 < (size incl - 1).+1 | 
  (i0 != (@inord  (size incl - 1) (index i incl))) &&
  ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
     w (t_eps + j) (i, nth i incl i0)) *
 (A_m + eps_j j eps_0 eps a))%Re.
Proof.
intros. rewrite (@big_cond_simpl_gt i incl (fun i0:nat => (x_general mal init A (t_eps + j) (nth i incl i0) *
                    w (t_eps + j) (i, nth i incl i0))%Re)).
rewrite (@big_cond_simpl_gt i incl (fun i0:nat =>  w (t_eps + j) (i, nth i incl i0))).
apply Rle_ge. apply /RleP.
assert (((\sum_(i0 < (size incl - 1).+1 | 
              ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                 w (t_eps + j) (i, nth i incl i0)) *
            (A_m + eps_j j eps_0 eps a))%Re = 
          \sum_(i0 < (size incl - 1).+1 | 
              ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                 ((w (t_eps + j) (i, nth i incl i0)) *
            (A_m + eps_j j eps_0 eps a))%Re).
{ by rewrite big_distrl //=. } rewrite H4.
apply big_sum_ge_ex_abstract.
intros. rewrite Rmult_comm. apply Rmult_le_compat_r.
+ apply Rle_trans with a.
  - by apply Rlt_le.
  - apply H3. apply mem_nth.
    apply ltn_leq_trans with (size incl - 1).+1.
    ++ by apply ltn_ord.
    ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
       rewrite ltn_subrL. apply /andP. split.
       - by [].
       - apply H6.
+ apply Rle_trans with (x_general mal init A (t_eps + j) i).
  - apply Rge_le, H2.
  - assert (sorted_Dseq_general (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)%N)).
    { apply lemma_1.incl_sorted_general. } rewrite /sorted_Dseq_general in H6.
    apply H6.
    * apply i_in_incl_general.
    * rewrite -/incl. apply mem_nth.
      apply ltn_leq_trans with (size incl - 1).+1.
      ++ by apply ltn_ord.
      ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
         rewrite ltn_subrL. apply /andP. split.
         - by [].
         - apply H7.
  - rewrite index_uniq.
    * rewrite -/incl. rewrite inordK in H5.
      ++ apply H5.
      ++ rewrite subn1. rewrite prednK.
         - rewrite index_mem. apply i_in_incl_general.
         - apply size_incl_not_0_general.
    * apply ltn_leq_trans with (size incl - 1).+1.
      ++ by apply ltn_ord.
      ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
         rewrite ltn_subrL. apply /andP. split.
         - by [].
         - apply H7.
    * apply incl_uniq_general.
Qed.


(** i should not be the last element of incl **)
Lemma w_ih_ge_a (i:D) (a A_m A_M:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  (0 < a)%Re -> (a < 1)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
  (index i incl < (size incl).-1)%N ->
  let w_ih := \sum_(i0 < (size incl - 1).+1 | ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                w (t_eps + j) (i, nth i incl i0) in 
  (a <= w_ih)%Re.
Proof.
intros. rewrite /w_ih.
apply Rle_trans with (\sum_(i0 < (size incl - 1).+1 |
           ((@inord (size incl - 1) (index i incl)) < i0)%N) a).
+ apply sum_ge_a.
  - by [].
  - apply /hasP. simpl.
    exists (@inord (size incl - 1) (size incl).-1).
    * apply mem_index_enum. 
    * rewrite !inordK.
      ++ by [].
      ++ rewrite subn1. rewrite !prednK.
         - by [].
         - apply size_incl_not_0_general.
      ++ rewrite subn1. rewrite !prednK.
         - rewrite index_mem. apply i_in_incl_general.
         - apply size_incl_not_0_general.
+ apply /RleP. apply big_sum_ge_ex_abstract. intros.
  apply H1. apply mem_nth.
  apply ltn_leq_trans with (size incl - 1).+1.
  ++ by apply ltn_ord.
  ++ assert ((0< size incl)%N). { apply size_incl_not_0_general. }
     rewrite ltn_subrL. apply /andP. split.
     - by [].
     - apply H5.
Qed.



Lemma x_val_increases_1 (i:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta m_general mal init A] A_m ->
  (0<N)%N-> (j<=N)%N -> 
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (x_general mal init A (t_eps + j) i >= A_m + eps_j j eps_0 eps a)%Re ->
  (x_general mal init A (t_eps + j.+1) i >=  A_m + eps_j j.+1 eps_0 eps a)%Re.
Proof.
intros. simpl. 
assert ((t_eps + j.+1)%N = (t_eps + j).+1).
{ by rewrite -addn1 addnA addn1. } rewrite H13.
simpl.
assert (A i = false).
{ rewrite !inE in H5. simpl in H5. 
  assert ( (A i != true) /\ true).
  { by apply /andP. } destruct H14. 
  by destruct (A i).
} rewrite H14 //=.
rewrite sum_f_R0_big_equiv. rewrite -/incl.
assert ((index i incl <= (size incl).-1)%N).
{ apply ltnSE. rewrite prednK.
  + rewrite index_mem. apply i_in_incl_general.
  + apply size_incl_not_0_general.
} rewrite leq_eqVlt in H15.
assert ((index i incl == (size incl).-1)
          \/ (index i incl < (size incl).-1)%N).
{ by apply /orP. } destruct H16.
++ rewrite (bigD1 (inord (index i incl))) //=. 
   rewrite inordK.
   + rewrite nth_index.
     - rewrite -RplusE.
       assert (\sum_(i0 < (size incl - 1).+1 | i0
                                 != 
                                 inord
                                 (index i incl))
                (x_general mal init A (t_eps + j) (nth i incl i0) *
                 w (t_eps + j) (i, nth i incl i0))%Re = 
              \sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&(i0
                                 <
                                 @inord (size incl-1)
                                 (index i incl))%N)
                  (x_general mal init A (t_eps + j) (nth i incl i0) *
                   w (t_eps + j) (i, nth i incl i0))%Re).
       { apply eq_big.
         + unfold eqfun. intros. 
           assert (index i incl = (size incl).-1).
           { by apply /eqP. } rewrite H17. rewrite neq_ltn.
           assert ((@inord (size incl-1) (size incl).-1 < x)%N = false).
           { apply leq_gtF. rewrite inordK.
             + apply ltnSE. rewrite prednK.
               - apply ltn_leq_trans with (size incl -1).+1. 
                 * apply ltn_ord.
                 * rewrite subn1 ltn_predL. apply size_incl_not_0_general.
               - apply size_incl_not_0_general.
             + rewrite subn1. rewrite prednK.
               - by [].
               - apply size_incl_not_0_general.
           } rewrite H18. by destruct (x < inord (size incl).-1)%N.
         + by intros.
       } rewrite H17. clear H17. 
       apply Rge_trans with 
        (x_general mal init A (t_eps + j) i * w (t_eps + j) (i, i) +
          (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
          (i0 < (@inord  (size incl - 1) (index i incl)))%N)
             w (t_eps + j) (i, nth i incl i0)) * m_general mal init A (t_eps + j))%Re.
       * apply Rplus_ge_compat_l. rewrite /incl.
         by apply (@x_left_ineq_2 i a A_m t_eps j eps eps_0).
       * apply Rge_trans with 
          ((A_m + eps_j j eps_0 eps a) * w (t_eps + j) (i, i) +
               (\sum_(i0 < (size incl - 1).+1 | 
                (i0 != @inord (size incl-1) (index i incl)) &&
                (i0 < @inord (size incl -1) (index i incl))%N)
                   w (t_eps + j) (i, nth i incl i0)) *
               m_general mal init A (t_eps + j))%Re.
         ++ apply Rplus_ge_compat_r. apply Rmult_ge_compat_r.
            + apply Rle_ge. apply Rle_trans with a.
              - nra.
              - apply H9. apply i_in_incl_general.
            + by [].
         ++ assert (( A_m + (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re = 
                      ((1-a)* (A_m - eps) + a * (A_m + eps_j j eps_0 eps a))%Re).
            { nra. } rewrite H17.
            assert ((\sum_(i0 < (size incl - 1).+1 | 
                      (i0 != @inord (size incl -1) (index i incl)) &&
                      (i0 < @inord (size incl-1) (index i incl))%N)
                         w (t_eps + j) (i, nth i incl i0)) = 
                    (1 - w (t_eps + j) (i, i))%Re).
            { assert ((\sum_(i0 < (size incl - 1).+1 | 
                      (i0 != @inord (size incl -1) (index i incl)) &&
                      (i0 < @inord (size incl-1) (index i incl))%N)
                         w (t_eps + j) (i, nth i incl i0)) = 
                    (1 - w (t_eps + j) (i, i))%Re <-> 
                      (w (t_eps + j) (i, i) + 
                        \sum_(i0 < (size incl - 1).+1 | 
                      (i0 != @inord (size incl -1) (index i incl)) &&
                      (i0 < @inord (size incl-1) (index i incl))%N)
                         w (t_eps + j) (i, nth i incl i0))%Re = 1%Re).
              { nra. } rewrite H18. clear H18.
              rewrite sum_f_R0_big_equiv in H10. rewrite -H10.
              rewrite [in RHS](bigD1 (inord (index i incl))) //=.
              rewrite inordK.
              + rewrite nth_index.
                - rewrite -RplusE. apply Rplus_eq_compat_l.
                  apply eq_big.
                  * unfold eqfun. intros.
                    assert (index i incl = (size incl).-1).
                   { by apply /eqP. } rewrite H18. rewrite neq_ltn.
                   assert ((@inord (size incl-1) (size incl).-1 < x)%N = false).
                   { apply leq_gtF. rewrite inordK.
                     + apply ltnSE. rewrite prednK.
                       - apply ltn_leq_trans with (size incl -1).+1. 
                         * apply ltn_ord.
                         * rewrite subn1 ltn_predL. apply size_incl_not_0_general.
                       - apply size_incl_not_0_general.
                     + rewrite subn1. rewrite prednK.
                       - by [].
                       - apply size_incl_not_0_general.
                   } rewrite H19. rewrite inordK.
                   ++ by destruct  (x < (size incl).-1)%N.
                   ++ rewrite subn1. rewrite prednK.
                      - by [].
                      - apply size_incl_not_0_general.
                  * by intros.
                 - apply i_in_incl_general.
               + rewrite subn1. rewrite prednK.
                 - rewrite index_mem. apply i_in_incl_general.
                 - apply size_incl_not_0_general.
             } rewrite H18. clear H18.
              remember (w (t_eps + j) (i, i)) as w_ii.
              assert ((m_general mal init A (t_eps+j)%N > A_m - eps)%Re). 
              { apply H11. apply /leP. apply leq_addr. }
              apply Rge_trans with ((1 - a) * m_general mal init A (t_eps + j)%N +
                                      a * (A_m + eps_j j eps_0 eps a))%Re.
              - assert (((A_m + eps_j j eps_0 eps a) * w_ii +
                          (1 - w_ii) * m_general mal init A (t_eps + j))%Re = 
                        (m_general mal init A (t_eps + j) - w_ii * ( m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a)))%Re).
                { nra. } rewrite H19.
                assert (((1 - a) * m_general mal init A (t_eps + j) +
                            a * (A_m + eps_j j eps_0 eps a))%Re = 
                         (m_general mal init A (t_eps + j) - a * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a)))%Re).
                { nra. } rewrite H20.
                apply Rplus_ge_compat_l. 
                assert ((- (w_ii * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a))))%Re = 
                          (w_ii * ((A_m + eps_j j eps_0 eps a) - m_general mal init A (t_eps + j)))%Re). { nra. }
                rewrite H21. clear H21.
                assert ((-(a * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a))))%Re = 
                           (a * ((A_m + eps_j j eps_0 eps a) - m_general mal init A (t_eps + j)))%Re). { nra. }
                rewrite H21. clear H21. apply Rle_ge. 
                apply Rmult_le_compat_r.
                * apply Rge_le, Rge_minus. apply Rle_ge. apply Rle_trans with A_m.
                  ++ by apply m_A_m_lower_bound. 
                  ++ assert ((0 < eps_j j eps_0 eps a)%Re).
                     { by apply eps_j_gt_0 with N.  } nra.
                *  rewrite Heqw_ii. apply H9 . apply i_in_incl_general.
              - apply  Rplus_ge_compat_r, Rmult_ge_compat_l.
                + nra. 
                + by apply Rle_ge, Rlt_le.
           - apply i_in_incl_general.
  + rewrite subn1. rewrite prednK.
    - rewrite index_mem.  apply i_in_incl_general.
    - rewrite -has_predT. apply /hasP. exists i.
      * apply i_in_incl_general.
      * by [].
++ rewrite (bigD1 (inord (index i incl))) //=. 
  rewrite inordK.
  + rewrite nth_index. 
    - rewrite -RplusE. 
      apply Rge_trans with ((m_general mal init A (t_eps +j)%N) * w (t_eps + j) (i, i) +
           \sum_(i0 < (size incl - 1).+1 | 
           i0 != inord (index i incl))
              (x_general mal init A (t_eps + j) (nth i incl i0) *
               w (t_eps + j) (i, nth i incl i0))%Re).
      * apply Rplus_ge_compat_r, Rmult_ge_compat_r.
        ++ specialize (H9 i).
           assert (i \in incl). {  apply i_in_incl_general. }
           specialize (H9 H17). apply Rle_ge.
           apply Rlt_le. by apply Rlt_le_trans with a.
        ++ apply Rle_ge. by apply x_bound.
      * rewrite -RplusE -RmultE.
        rewrite (@big_nat_split i incl  
                  (fun i0 :nat => (x_general mal init A (t_eps + j) (nth i incl i0) *
                      w (t_eps + j) (i, nth i incl i0))%Re)).
        apply Rge_trans with
        (m_general mal init A (t_eps + j) * w (t_eps + j) (i, i) +  
          (((\sum_(i0 < (size incl - 1).+1 | 
                (i0 != (@inord  (size incl - 1) (index i incl))) &&
                (i0 < (@inord (size incl - 1) (index i incl)))%N)
                    w (t_eps + j) (i, nth i incl i0)) * (m_general mal init A (t_eps+j)%N))%Re +
          (\sum_(i0 < (size incl - 1).+1 | (i0
                                    != 
                                   (@inord  (size incl - 1) (index i incl))) &&
                                    ~~
                                    (i0 <
                                    (@inord  (size incl - 1) (index i incl)))%N)
             (x_general mal init A (t_eps + j) (nth i incl i0) *
              w (t_eps + j) (i, nth i incl i0))%Re)%Ri))%Re.
         ++ apply Rplus_ge_compat_l. rewrite -RplusE. apply Rplus_ge_compat_r.
            rewrite /incl. by apply (@x_left_ineq_2 i a A_m t_eps j eps eps_0).
         ++ apply Rge_trans with
            (m_general mal init A (t_eps + j) * w (t_eps + j) (i, i) +
             ((\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                               (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                  w (t_eps + j) (i, nth i incl i0)) * m_general mal init A (t_eps+j)
               +
              (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                              ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                  w (t_eps + j) (i, nth i incl i0)) * (A_m + eps_j j eps_0 eps a)))%Re.
            * apply Rplus_ge_compat_l. apply Rplus_ge_compat_l.
              rewrite /incl. by apply (@x_right_ineq_2 i a A_m t_eps j eps eps_0). 
            * assert ((m_general mal init A (t_eps + j) * w (t_eps + j) (i, i) +
                       ((\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0)) * m_general mal init A (t_eps+j)%N
                         +
                        (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0)) * (A_m + eps_j j eps_0 eps a)))%Re = 
                       ((w (t_eps + j) (i, i) +  (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0))) * m_general mal init A (t_eps+j)%N + 
                        (\sum_(i0 < (size incl - 1).+1 | (i0 != (@inord  (size incl - 1) (index i incl))) &&
                                                         ~~ (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0))   
                        * (A_m + eps_j j eps_0 eps a))%Re).
              { nra. } rewrite H17.  clear H17.
              assert (( A_m + (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re = 
                      ((1-a)* (A_m - eps) + a * (A_m + eps_j j eps_0 eps a))%Re).
              { nra. } rewrite H17.
              rewrite (@big_cond_simpl_gt i incl (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
              rewrite (@big_cond_simpl_lt i incl (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
              assert ((w (t_eps + j) (i, i) +
                        \sum_(i0 < (size incl - 1).+1 | 
                        (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                           w (t_eps + j) (i, nth i incl i0))%Re =
                      (1 - (\sum_(i0 < (size incl - 1).+1 | 
                            ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                               w (t_eps + j) (i, nth i incl i0)))%Re).
              { assert ((w (t_eps + j) (i, i) +
                         \sum_(i0 < (size incl - 1).+1 | 
                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0))%Re =
                        (1 -
                         \sum_(i0 < (size incl - 1).+1 | 
                         ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                            w (t_eps + j) (i, nth i incl i0))%Re <-> 
                        (w (t_eps + j) (i, i) +
                         \sum_(i0 < (size incl - 1).+1 | 
                         (i0 < (@inord  (size incl - 1) (index i incl)))%N)
                            w (t_eps + j) (i, nth i incl i0) + \sum_(i0 < (size incl - 1).+1 | 
                         ((@inord  (size incl - 1) (index i incl)) < i0)%N)
                            w (t_eps + j) (i, nth i incl i0))%Re = 1%Re). { nra. }
                rewrite H18. clear H18. rewrite sum_f_R0_big_equiv in H10. rewrite -H10.
                rewrite [in RHS](bigD1 (inord (index i incl))) //=.
                rewrite inordK.
                + rewrite nth_index.
                  - rewrite Rplus_assoc. rewrite -[in RHS]RplusE.
                    apply Rplus_eq_compat_l. 
                    rewrite [in RHS](@big_nat_split i incl 
                        (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
                    rewrite (@big_cond_simpl_gt i incl 
                        (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
                    rewrite (@big_cond_simpl_lt i incl 
                        (fun i0:nat => w (t_eps + j) (i, nth i incl i0))).
                    rewrite inordK.
                    * by rewrite -RplusE Rplus_comm. 
                    * apply ltn_leq_trans with (size incl). 
                      ++ rewrite index_mem. apply i_in_incl_general.
                      ++ rewrite subn1. rewrite prednK.
                         + by [].
                         + apply size_incl_not_0_general.
                    * apply i_in_incl_general.
                + apply ltn_leq_trans with (size incl). 
                  - rewrite index_mem. apply i_in_incl_general.
                  - rewrite subn1. rewrite prednK.
                    * by [].
                    * apply size_incl_not_0_general.
              } rewrite H18.
              remember (\sum_(i0 < (size incl - 1).+1 | 
                          ( inord (index i incl) < i0)%N)
                             w (t_eps + j) (i, nth i incl i0)) as w_ih.
              assert ((m_general mal init A (t_eps+j)%N > A_m - eps)%Re). 
              { apply H11. apply /leP. apply leq_addr. }
              apply Rge_trans with ((1 - a) * m_general mal init A (t_eps + j)%N +
                                      a * (A_m + eps_j j eps_0 eps a))%Re.
              - assert (((1 - w_ih) * m_general mal init A (t_eps + j) +
                              w_ih * (A_m + eps_j j eps_0 eps a))%Re = 
                        (m_general mal init A (t_eps + j) - w_ih * ( m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a)))%Re).
                { nra. } rewrite H20.
                assert (((1 - a) * m_general mal init A (t_eps + j) +
                            a * (A_m + eps_j j eps_0 eps a))%Re = 
                         (m_general mal init A (t_eps + j) - a * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a)))%Re).
                { nra. } rewrite H21.
                apply Rplus_ge_compat_l. 
                assert ((- (w_ih * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a))))%Re = 
                          (w_ih * ((A_m + eps_j j eps_0 eps a) - m_general mal init A (t_eps + j)))%Re). { nra. }
                rewrite H22. clear H22.
                assert ((-(a * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a))))%Re = 
                           (a * ((A_m + eps_j j eps_0 eps a) - m_general mal init A (t_eps + j)))%Re). { nra. }
                rewrite H22. clear H22. apply Rle_ge. 
                apply Rmult_le_compat_r.
                * apply Rge_le, Rge_minus. apply Rle_ge. apply Rle_trans with A_m.
                  ++ by apply m_A_m_lower_bound.
                  ++ assert ((0 < eps_j j eps_0 eps a)%Re).
                     { by apply eps_j_gt_0 with N. } nra.
                *  rewrite Heqw_ih. by apply w_ih_ge_a .
              - apply  Rplus_ge_compat_r, Rmult_ge_compat_l.
                + nra. 
                + by apply Rle_ge, Rlt_le.
    - apply i_in_incl_general.
  + rewrite subn1. rewrite prednK.
    - rewrite index_mem.  apply i_in_incl_general.
    - rewrite -has_predT. apply /hasP. exists i.
      * apply i_in_incl_general.
      * by [].
Qed.


Lemma inord_pred2: forall (P Q R S: bool),
  R = false -> 
  P && (Q || R) = [&& S || P, P & Q].
Proof.
intros. destruct P.
+ simpl. destruct Q. 
  - simpl. by destruct S.
  - simpl. rewrite H. by destruct S.
+ simpl. by destruct S.
Qed.

Lemma big_split_lt_last  (i:D) (l : seq D) (F: nat -> R):
  l != [::] -> 
  uniq l -> 
  (0 < size l)%N ->
  (@inord (size l- 1) (index i l) <
      @inord (size l- 1) (index (last (head i l) (behead l)) l))%N ->
  \sum_(i0 < (size l - 1).+1 | (i0 != inord (index i l)) && 
                ~~(i0 < (@inord (size l- 1) (index i l)))%N) F i0 = 
(F (@inord (size l - 1) (index (last (head i l) (behead l)) l)) + 
  \sum_(i0 < (size l - 1).+1 | (i0 != inord (index i l)) && 
                    (@inord (size l- 1) (index i l) < i0 
                    < @inord (size l - 1) (index (last (head i l) (behead l)) l))%N) F i0)%Re.
Proof.
intros.
rewrite (@big_cond_simpl_gt i l F). 
rewrite [in LHS](bigD1 (@inord (size l - 1) (index (last (head i l) (behead l)) l))) //=.
rewrite -[in LHS]RplusE. apply Rplus_eq_compat_l.
apply eq_bigl. unfold eqfun. intros. rewrite !neq_ltn.
apply inord_pred2. apply leq_gtF.
assert (l = (head i l) :: (behead l)).
{ by apply list_dissect. } 
assert (@inord (size l - 1) (index (last (head i l) (behead l)) l) = 
        @inord (size l -1) (index (last (head i l) (behead l)) (head i l :: behead l))).
{ by rewrite H3. } rewrite H4. clear H4.
rewrite index_last.
+ rewrite inordK.
  - rewrite size_behead. apply ltnSE. rewrite -subn1. apply ltn_ord.
  - rewrite size_behead. rewrite subn1. by rewrite prednK.
+ by rewrite -H3.
Qed.


Lemma and_3_conv: forall (P Q R: bool),
  [&& P, Q & R] -> P /\ Q /\ R.
Proof.
intros. destruct P.
+ simpl in H. destruct Q.
  - simpl in H. by destruct R2.
  - by simpl in H.
+ by simpl in H.
Qed.



Lemma in_neighbor_subset_incl_last (i:D) (a A_m:R) (t_eps j:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  i \in Normal_general A ->
  (x_general mal init A (t_eps + j) i < A_m + eps_j j eps_0 eps a)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in 
  {subset (in_neighbor i  :\: 
                X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A) <= 
        [set x | x \in incl] :|: R_i_greater_than_general mal init A i (t_eps+j)%N}.
Proof.
intros. rewrite /sub_mem //=. move=> k.
intros. rewrite inE in H1. apply and_2_conv in H1.
destruct H1. rewrite inE in H1. rewrite in_setU. apply /orP.
rewrite inE. 
destruct (Rlt_dec (x_general mal init A (t_eps + j) k) (A_m + eps_j j eps_0 eps a)).
+ by simpl in H1.
+ simpl in H1. 
  assert ((index k (inclusive_neighbor_list i) <= size (inclusive_neighbor_list i) - F - 1)%N \/
           (size (inclusive_neighbor_list i) - F - 1  <= index k (inclusive_neighbor_list i))%N).
  { apply /orP. apply leq_total. }
  destruct H3.
  - left.
    rewrite /incl /incl_neigh_minus_extremes /remove_extremes //=.
    rewrite mem_filter. apply /andP. split.
    * apply /andP. split.
      ++ apply /orP. left.
         destruct (Rge_dec (x_general mal init A (t_eps + j) k) (x_general mal init A (t_eps + j) i)).
         - by simpl.
         - simpl.
           assert ((x_general mal init A (t_eps + j) k >= x_general mal init A (t_eps + j) i)%Re).
           { apply Rle_ge. apply Rle_trans with (A_m + eps_j j eps_0 eps a)%Re.
             + by apply Rlt_le.
             + by apply Rnot_gt_le in n.
           } contradiction.
      ++ apply /orP. by right.
    * rewrite /inclusive_neighbor_list /inclusive_neigh.
      assert (k \in (in_neighbor i :|: [set i])). 
      { rewrite in_setU. apply /orP. by left. }
      assert ([set x | x \in enum (in_neighbor i :|: [set i])] = (in_neighbor i :|: [set i])).
      { apply set_enum. } rewrite -H5 in H4.
      by rewrite inE in H4.
  - rewrite leq_eqVlt in H3.
    assert ((index k (inclusive_neighbor_list i) == (size (inclusive_neighbor_list i) - F - 1)%N)
              \/ (size (inclusive_neighbor_list i) - F - 1 <
                      index k (inclusive_neighbor_list i))%N).
    { rewrite eq_sym in H3. by apply /orP. } destruct H4. 
    * assert (index k (inclusive_neighbor_list i) = (size (inclusive_neighbor_list i) - F - 1)%N).
      { by apply /eqP. }
      left. rewrite /incl /incl_neigh_minus_extremes /remove_extremes //=.
      rewrite mem_filter. apply /andP. split.
      ++ apply /andP. split.
         - apply /orP. left.
           destruct (Rge_dec (x_general mal init A (t_eps + j) k) (x_general mal init A (t_eps + j) i)).
           * by simpl.
           * simpl.
             assert ((x_general mal init A (t_eps + j) k >= x_general mal init A (t_eps + j) i)%Re).
             { apply Rle_ge. apply Rle_trans with (A_m + eps_j j eps_0 eps a)%Re.
               + by apply Rlt_le.
               + by apply Rnot_gt_le in n.
             } contradiction.
         - apply /orP. right. by rewrite H5.
      ++ rewrite /inclusive_neighbor_list /inclusive_neigh.
          assert (k \in (in_neighbor i :|: [set i])). 
          { rewrite in_setU. apply /orP. by left. }
          assert ([set x | x \in enum (in_neighbor i :|: [set i])] = (in_neighbor i :|: [set i])).
          { apply set_enum. } rewrite -H7 in H6.
          by rewrite inE in H6.
    * right. rewrite inE. apply /andP. split.
      ++ apply /andP. split.
         - destruct (Rgt_dec (x_general mal init A (t_eps + j) k) (x_general mal init A (t_eps + j) i)).
           * by simpl.
           * simpl.
             assert ((x_general mal init A (t_eps + j) k > x_general mal init A (t_eps + j) i)%Re).
             { apply Rlt_gt. apply Rlt_le_trans with (A_m + eps_j j eps_0 eps a)%Re.
               + by [].
               + by apply Rnot_gt_le in n.
             } contradiction.
         - by [].
      ++ rewrite /inclusive_neighbor_list /inclusive_neigh.
          assert (k \in (in_neighbor i :|: [set i])). 
          { rewrite in_setU. apply /orP. by left. }
          assert ([set x | x \in enum (in_neighbor i :|: [set i])] = (in_neighbor i :|: [set i])).
          { apply set_enum. } rewrite -H6 in H5.
           by rewrite inE in H5.
Qed.

Lemma s_subset_incl_last (i:D) (a A_m:R) (t_eps j:nat) (eps eps_0: posreal) (s: seq D)
  (mal : nat ->D ->R) (init : D -> R) (A : D -> bool): 
  i \in Normal_general A ->
  (x_general mal init A (t_eps + j) i < A_m + eps_j j eps_0 eps a)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in 
  {subset s <= in_neighbor i  :\: 
                X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A} ->
  {subset s <= [set x | x \in incl] :|: R_i_greater_than_general mal init A i (t_eps+j)%N}.
Proof.
intros.
assert ({subset [set x | x \in s] <= [set x | x \in incl] :|: R_i_greater_than_general mal init A i (t_eps+j)%N}).
{ apply /subsetP.
  apply (@subset_trans D [set x | x \in s] 
   (in_neighbor i  :\: 
                  X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A)
    ([set x | x \in incl] :|: R_i_greater_than_general mal init A i (t_eps+j)%N)). 
  + apply /subsetP. rewrite /sub_mem //=. intros.
    rewrite inE in H2. rewrite /sub_mem in H1. 
    by specialize (H1 x H2).
  + rewrite /incl. apply /subsetP. by apply in_neighbor_subset_incl_last.
} rewrite /sub_mem //=. intros. rewrite /sub_mem in H2.
specialize (H2 x). rewrite inE in H2. by specialize (H2 H3).
Qed.




Lemma k_in_incl_bounded_m (i:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init  ->
  is_lim_seq [eta m_general mal init A] A_m -> 
  (0<N)%N-> (j<=N)%N ->
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (F + 1 <= #|in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A|)%N ->
  (x_general mal init A (t_eps + j) i < A_m + eps_j j eps_0 eps a)%Re ->
  (forall k: 'I_(size incl - 1).+1,
               (x_general mal init A (t_eps + j) (nth i incl k) >= m_general mal init A (t_eps + j))%Re).
Proof.
intros.
assert ((k <= @inord (size incl-1) (index i incl))%N \/
        (k >= @inord (size incl-1) (index i incl))%N).
{ apply /orP. apply leq_total. }
destruct H13.
+ apply Rle_ge.
  assert ((nth i incl k) \in Normal_general A \/ (nth i incl k) \in Adversary_general A).
  { apply normal_or_adversary. }
  destruct H14.
  - by apply x_bound.
  - assert ((#|R_i_less_than_general mal init A i (t_eps + j)%N| <= F)%N).
    { apply R_i_lt_bounded_general . } rewrite leq_eqVlt in H15.
    assert ( (#|R_i_less_than_general mal init A i (t_eps + j)| == F)
              \/ (#|R_i_less_than_general mal init A i (t_eps + j)| < F)%N).
    { by apply /orP. } destruct H16.
    * assert(R_i_less_than_general mal init A i (t_eps + j) == Adversary_general A \/
                  R_i_less_than_general mal init A i (t_eps + j) != Adversary_general A).
      { apply /orP.
        by destruct (R_i_less_than_general mal init A i (t_eps + j) == Adversary_general A).
      } destruct H17.
      ++ assert (R_i_less_than_general mal init A i (t_eps + j) == Adversary_general A ->
                  nth i incl k \notin Adversary_general A).
         { by apply incl_R_lt_does_not_contain_adversary. } specialize (H18 H17). 
         assert (~ (nth i incl k \in Adversary_general A)).
         { by apply /negP. } contradiction.
      ++ assert (exists k:D, k \in (Normal_general A :&: (R_i_less_than_general mal init A  i (t_eps+j)%N))).
        { by apply exists_an_elem_in_out_set_R_lt with k.  } destruct H18 as [p H18]. rewrite in_setI in H18.
        assert ((p \in Normal_general A) /\
                     (p \in R_i_less_than_general mal init A i (t_eps + j))).
        { by apply /andP. } destruct H19.
        apply Rle_trans with (x_general mal init A (t_eps + j) p).
        * by apply x_bound.
        * apply R_i_lt_val_rel with i.
          ++ rewrite -/incl. apply mem_nth.
             apply ltn_leq_trans with (size incl - 1).+1.
             + by apply ltn_ord.
             + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
               rewrite ltn_subrL. apply /andP. split.
               - by [].
               - apply H21.
          ++ apply H20.
    * (** The last node has the value same as x_i(t) and since i is Normal,
        x_i <= M **)
      apply Rle_trans with (x_general mal init A (t_eps + j)%N (nth i (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)) 0)).
      - assert (((x_general mal init A (t_eps+j) (nth i (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)) 0)) = (x_general mal init A (t_eps + j) i))%Re).
        { by apply  card_R_i_lt_lt_F_exchange_first_general. } rewrite H17.
        by apply x_bound.
      - apply first_incl_is_min_general. rewrite -/incl. apply mem_nth.
        apply ltn_leq_trans with (size incl - 1).+1.
        + by apply ltn_ord.
        + assert ((0< size incl)%N). { apply size_incl_not_0_general. }
          rewrite ltn_subrL. apply /andP. split.
          - by [].
          - apply H17.
+ rewrite leq_eqVlt in H13.
  assert ( (@inord (size incl -1) (index i incl) == k)
             \/ ( @inord (size incl -1) (index i incl)< k)%N).
  { by apply /orP. } destruct H14.
  - assert (k = inord (index i incl)).
    { rewrite eq_sym in H14. by apply /eqP. } rewrite H15.
    rewrite inordK.
    * rewrite nth_index.
      ++ by apply Rle_ge, x_bound.
      ++ apply i_in_incl_general.
    * rewrite subn1 prednK.
      ++ rewrite index_mem. apply i_in_incl_general.
      ++ apply size_incl_not_0_general.
  - apply Rle_ge.
    apply Rle_trans with  (x_general mal init A (t_eps + j) (nth i incl (@inord (size incl -1) (index i incl))))%Re.
    * rewrite inordK.
      ++ rewrite nth_index.
         - by apply x_bound.
         - apply i_in_incl_general.
      ++ rewrite subn1 prednK. rewrite index_mem. apply i_in_incl_general. apply size_incl_not_0_general.
    * rewrite inordK.
      ++ rewrite nth_index.
         - assert (sorted_Dseq_general incl).
           { apply lemma_1.incl_sorted_general. } rewrite /sorted_Dseq_general in H15.
           apply H15.
           * apply i_in_incl_general.
           * apply mem_nth. apply ltn_leq_trans with (size incl - 1).+1.
             ++ apply ltn_ord.
             ++ rewrite subn1. rewrite ltn_predL. apply size_incl_not_0_general.
           * rewrite index_uniq.
             ++ rewrite inordK in H14.
                - by [].
                - rewrite subn1 prednK.
                  * rewrite index_mem. apply i_in_incl_general.
                  * apply size_incl_not_0_general.
             ++ apply ltn_leq_trans with (size incl - 1).+1.
                - apply ltn_ord.
                - rewrite subn1. rewrite ltn_predL. apply size_incl_not_0_general.
             ++ apply incl_uniq_general.
         - apply i_in_incl_general.
      ++ rewrite subn1 prednK. rewrite index_mem. apply i_in_incl_general. apply size_incl_not_0_general.
Qed.


Lemma x_not_k_bound_m (i k:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal) (s: seq D)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init ->
  is_lim_seq [eta m_general mal init A] A_m -> 
  (0<N)%N-> (j<=N)%N ->
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (F + 1 <= #|in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A|)%N ->
  (x_general mal init A (t_eps + j) i < A_m + eps_j j eps_0 eps a)%Re ->
  {subset s
           <= in_neighbor i
              :\: X_m_t_e_i (eps_j j eps_0 eps a)
                    A_m (t_eps + j) mal init A} ->
  k \in incl ->
  k \in s ->
  (\sum_(i0 < (size incl - 1).+1 | 
 i0 != inord (index k incl))
    (x_general mal init A (t_eps + j) (nth i incl i0) *
     w (t_eps + j) (i, nth i incl i0))%Re >=
 (\sum_(i0 < (size incl - 1).+1 | 
  i0 != inord (index k incl))
     w (t_eps + j) (i, nth i incl i0)) *
  m_general mal init A (t_eps + j))%Re.
Proof.
intros.
assert (((\sum_(i0 < (size incl - 1).+1 | 
          i0 != inord (index k incl))
             w (t_eps + j) (i, nth i incl i0)) *
         m_general mal init A (t_eps + j))%Re = 
       \sum_(i0 < (size incl - 1).+1 | 
          i0 != inord (index k incl))
             (w (t_eps + j) (i, nth i incl i0) * m_general mal init A (t_eps+j))%Re).
{ by rewrite big_distrl //=. } rewrite H16. apply Rle_ge. apply /RleP.
apply big_sum_ge_ex_abstract. intros.
rewrite Rmult_comm. apply Rmult_le_compat_r.
+ apply Rle_trans with a.
  - nra.
  - apply H8. apply mem_nth. 
    apply ltn_leq_trans with (size incl - 1).+1 .
    * apply ltn_ord.
    * rewrite subn1. rewrite ltn_predL. apply size_incl_not_0_general.
+ assert (i0 != @inord (size incl -1) (index k incl) :> nat).
  { by []. } rewrite inordK in H18.
  - assert (forall k: 'I_(size incl - 1).+1,
               (x_general mal init A (t_eps + j) (nth i incl k) >= m_general mal init A (t_eps + j))%Re).
    { by apply k_in_incl_bounded_m with a A_m A_M N eps eps_0.  } apply Rge_le. apply H19.
  - rewrite subn1 prednK.
    * by rewrite index_mem.
    * apply size_incl_not_0_general.
Qed.

Lemma x_in_incl_not_X_m (i:D) (a A_m:R) (t_eps j:nat) (eps eps_0: posreal)
 (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  forall (k:D),
  (k \in (in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j)%N mal init A)) ->
    (x_general mal init A (t_eps+j)%N k >= (A_m + eps_j j eps_0 eps a))%Re. 
Proof.
intros. rewrite in_setD in H. apply and_2_conv in H.
destruct H.
rewrite inE in H.
destruct ( Rlt_dec (x_general mal init A (t_eps + j) k)
                (A_m + eps_j j eps_0 eps a)).
+ by simpl in H.
+ simpl in H. by apply Rnot_lt_ge in n.
Qed.

Lemma x_val_increases_2 (i:D) (a A_m A_M:R) (t_eps j N:nat) (eps eps_0: posreal)
  (mal : nat -> D ->R) (init : D -> R) (A : D -> bool):
  F_total_malicious_general mal init A -> 
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta m_general mal init A] A_m ->
  (0<N)%N-> (j<=N)%N ->  
   i \in Normal_general A ->(0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  let incl :=  incl_neigh_minus_extremes i (x_general mal init A)
            (t_eps + j) in
  (forall k:D, k \in incl -> (a <= w (t_eps + j)%N  (i, k))%Re) ->
  sum_f_R0
    (fun n : nat =>  w (t_eps + j) (i, nth i incl n)) (size incl - 1) = 1%Re ->
   (forall t : nat,
     (t >= t_eps)%coq_nat ->
     (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (F + 1 <= #|in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A|)%N ->
  (x_general mal init A (t_eps + j) i < A_m + eps_j j eps_0 eps a)%Re ->
  (x_general mal init A (t_eps + j.+1) i >=  A_m + eps_j j.+1 eps_0 eps a)%Re.
Proof.
intros.  simpl. 
assert ((t_eps + j.+1)%N = (t_eps + j).+1).
{ by rewrite -addn1 addnA addn1. } rewrite H14.
simpl.
assert (A i = false).
{ rewrite !inE in H5. simpl in H5. 
  assert ( (A i != true) /\ true).
  { by apply /andP. } destruct H15. 
  by destruct (A i).
} rewrite H15 //=.
rewrite sum_f_R0_big_equiv. rewrite -/incl.
assert (exists s, [/\ uniq s, size s = (F+1)%N & 
              {subset s <= (in_neighbor i :\: X_m_t_e_i  (eps_j j eps_0 eps a) A_m (t_eps+j)%N mal init A)}]).
{ by apply /card_geqP. } destruct H16 as [s H16].
destruct H16.
assert (exists k:D, k \in [set x | x \in s] :&: [set x | x \in incl]).
{ apply exists_in_intersection with (R_i_greater_than_general mal init A i (t_eps+j)%N) F.
  + assert (#|s| = size s). { by apply /card_uniqP. }
    by rewrite H19.
  + apply R_i_gt_bounded_general.
  + by apply s_subset_incl_last with a A_m eps eps_0.
} destruct H19 as [k H19].
rewrite in_setI !inE in H19.
    assert ( (k \in s) /\ (k \in incl)).
    { by apply /andP. } destruct H20.
rewrite (bigD1 (inord (index k incl))) //=.
rewrite inordK.
+ rewrite nth_index.
  - rewrite -RplusE.
    assert ((\sum_(i0 < (size incl - 1).+1 | 
             i0 != inord (index k incl))
                (x_general mal init A (t_eps + j) (nth i incl i0) *
                 w (t_eps + j) (i, nth i incl i0))%Re >=
            ((\sum_(i0 < (size incl - 1).+1 | 
                i0 != inord (index k incl))  w (t_eps + j) (i, nth i incl i0)) *
             m_general mal init A (t_eps+j))%Re)%Re).
    { by apply x_not_k_bound_m with a A_m A_M N eps eps_0 s. } apply Rle_ge.
   apply Rle_trans with 
    (x_general mal init A (t_eps + j) k * w (t_eps + j) (i, k) + 
      ((\sum_(i0 < (size incl - 1).+1 | 
        i0 != inord (index k incl))
           w (t_eps + j) (i, nth i incl i0)) *
       m_general mal init A (t_eps + j))%Re)%Re.
   * apply Rle_trans with 
      ( (w (t_eps + j) (i, k) * (A_m + eps_j j eps_0 eps a))%Re+
         (\sum_(i0 < (size incl - 1).+1 | 
          i0 != inord (index k incl))
             w (t_eps + j) (i, nth i incl i0)) *
         m_general mal init A (t_eps + j))%Re.
     ++ assert (( A_m + (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re = 
                      ((1-a)* (A_m - eps) + a * (A_m + eps_j j eps_0 eps a))%Re).
        { nra. } rewrite H23.
        assert (\sum_(i0 < (size incl - 1).+1 | 
                  i0 != inord (index k incl))
                     w (t_eps + j) (i, nth i incl i0) = 
                (1 - w (t_eps + j) (i, k))%Re).
        { assert (\sum_(i0 < (size incl - 1).+1 | i0
                                != 
                                inord
                                (index k incl))
                       w (t_eps + j) (i, nth i incl i0) =
                    (1 - w (t_eps + j) (i, k))%Re <->
                  (w (t_eps + j) (i, k) + 
                    \sum_(i0 < (size incl - 1).+1 | i0
                                != 
                                inord
                                (index k incl))
                       w (t_eps + j) (i, nth i incl i0))%Re = 1%Re).
          { nra. } rewrite H24. clear H24.
          rewrite sum_f_R0_big_equiv in H10. rewrite -H10.
          rewrite [in RHS](bigD1 (inord (index k incl))) //=.
          rewrite inordK.
          + by rewrite nth_index.
          + rewrite subn1 prednK. rewrite index_mem.
            - by [].
            - apply size_incl_not_0_general.
        } rewrite H24. clear H24.
        remember (w (t_eps + j) (i, k)) as w_ik.
        assert ((m_general mal init A (t_eps+j)%N > A_m - eps)%Re). 
        { apply H11. apply /leP. apply leq_addr. }
        apply Rle_trans with ((1 - a) * m_general mal init A (t_eps + j)%N +
                                      a * (A_m + eps_j j eps_0 eps a))%Re.
        - apply  Rplus_le_compat_r, Rmult_le_compat_l.
          + nra. 
          + by apply Rlt_le.
        - assert ((w_ik * (A_m + eps_j j eps_0 eps a) +
                  (1 - w_ik) * m_general mal init A (t_eps + j))%Re = 
                        (m_general mal init A (t_eps + j) - w_ik * ( m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a)))%Re).
          { nra. } rewrite H25.
          assert (((1 - a) * m_general mal init A (t_eps + j) +
                            a * (A_m + eps_j j eps_0 eps a))%Re = 
                         (m_general mal init A (t_eps + j) - a * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a)))%Re).
          { nra. } rewrite H26.
          apply Rplus_le_compat_l. 
          assert ((- (w_ik * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a))))%Re = 
                          (w_ik * ((A_m + eps_j j eps_0 eps a) - m_general mal init A (t_eps + j)))%Re). { nra. }
          rewrite H27. clear H27.
          assert ((-(a * (m_general mal init A (t_eps + j) - (A_m + eps_j j eps_0 eps a))))%Re = 
                           (a * ((A_m + eps_j j eps_0 eps a) - m_general mal init A (t_eps + j)))%Re). { nra. }
          rewrite H27. clear H27. 
          apply Rmult_le_compat_r.
          * apply Rge_le, Rge_minus. apply Rle_ge. apply Rle_trans with A_m.
            ++ by apply m_A_m_lower_bound. 
            ++ assert ((0 < eps_j j eps_0 eps a)%Re).
               { by apply eps_j_gt_0 with N.  } nra.
          * rewrite Heqw_ik. by apply H9.
       ++ apply Rplus_le_compat_r. rewrite Rmult_comm. apply Rmult_le_compat_r.
        - apply Rle_trans with a.
          * nra.
          * by apply H9.
        - apply Rge_le, x_in_incl_not_X_m with i. rewrite /sub_mem in H17.
          by specialize (H18 k H20).
    * apply Rplus_le_compat_l. apply Rge_le. by apply x_not_k_bound_m with a A_m A_M N eps eps_0 s.
  - by [].
+ rewrite subn1. rewrite prednK.
  - by rewrite index_mem. 
  - apply size_incl_not_0_general.
Qed.


Lemma enum_to_set_mem: forall (i:D) (l : {set D}),
  i \in l -> i \in enum l.
Proof.
intros.
assert (l = [set k | k \in enum l]).
{ by rewrite set_enum. } rewrite H0 in H.
by rewrite inE in H.
Qed.


Lemma bool_rel: forall (P Q R : bool),
   (R -> Q) ->
  ~~(R && P && Q) && R = (R && ~~P && Q).
Proof.
intros. destruct P.
+ simpl. destruct R2.
  - simpl. destruct Q.
    * by simpl.
    * simpl. assert (true ). { by [].  } by specialize (H H0).
  - by simpl.
+ simpl. destruct R2.
  - simpl. by rewrite H.
  - by simpl.
Qed. 


Lemma X_M_size_decreases_from_0_1 
  (t_eps: nat) (a A_m A_M:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A : D -> bool): 
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init  ->
  (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta M_general mal init A] A_M ->
   (0 < a)%Re -> (a < 1)%Re ->
   (eps < a ^ #|Normal_general A| / (1 - a ^ #|Normal_general A|) * eps_0)%Re ->
  (forall i:D, (*i \in Normal ->  *)
     (forall k : D,
          k \in incl_neigh_minus_extremes i (x_general mal init A) (t_eps + 0) ->
          (a <= w (t_eps + 0) (i, k))%Re) /\
     (sum_f_R0
        (fun n0 : nat =>
         w (t_eps + 0)
           (i,
           nth i
             (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + 0))
             n0))
        (size (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + 0)) -
         1) = 1%Re)) ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) -> 
   (exists i:D, i \in (X_M_t_e_i eps_0 A_M t_eps mal init A) /\ i \in Normal_general A /\
                (F + 1 <=
                   #|in_neighbor i
                     :\: X_M_t_e_i (eps_j 0 eps_0 eps a) A_M
                           (t_eps + 0) mal init A|)%N ) -> 
  (#|X_M_t_e_i (eps_j 1 eps_0 eps a) A_M (t_eps + 1) mal init A
   :&: Normal_general A| <
   #|X_M_t_e_i (eps_j 0 eps_0 eps a) A_M t_eps mal init A
     :&: Normal_general A|)%N.
Proof.
intros.
apply proper_card. rewrite /proper. apply /andP.
split.
+ apply /subsetP. rewrite /sub_mem //=. move => i H9.
  rewrite in_setI in H9. rewrite in_setI. apply /andP.
  assert ( (i \in X_M_t_e_i (a * eps_0 - (1 - a) * eps)
             A_M (t_eps + 1) mal init A) /\ (i \in Normal_general A)).
  { by apply /andP. } destruct H10 as [H10 H11].
  split.
  - rewrite inE. rewrite inE in H10.
    destruct (Rgt_dec (x_general mal init A (t_eps + 1) i)
                (A_M - (a * eps_0 - (1 - a) * eps))).
    * simpl in H10. 
      destruct (Rgt_dec (x_general mal init A t_eps i) (A_M - eps_0)).
      ++ by simpl.
      ++ simpl. apply Rnot_gt_le in n.
         assert (( x_general mal init A (t_eps + 1) i <= A_M - (a * eps_0 - (1 - a) * eps))%Re).
         { apply (@x_val_decreases_1 i a A_m A_M t_eps 0%N #|Normal_general A| eps eps_0).
           + by [].
           + by [].
           + by [].
           + by [].
           + rewrite cardE. destruct H. by apply size_normal_gt_0.
           + apply ltnW. rewrite cardE. destruct H. by apply size_normal_gt_0.
           + by [].
           + by [].
           + by [].
           + by [].
           + specialize (H6 i). (*specialize (H6 i H11). *) by destruct H6.
           + specialize (H6 i). (*specialize (H6 i H11). *) by destruct H6.
           + by [].
           + by rewrite addn0 /eps_j.
         }
         apply Rle_not_gt in H12.
         contradiction.
    * by simpl in H10. 
  - apply H11.
+ apply /subsetPn. rewrite /eps_j. destruct H8 as [i H8].
  exists i. 
  - rewrite in_setI. apply /andP. destruct H8. destruct H9. by split. 
  - destruct H8 as [H8 H9].
    rewrite in_setI. apply /nandP. left.
    rewrite inE. rewrite inE in H8.
    destruct (Rgt_dec (x_general mal init A t_eps i) (A_M - eps_0)).
    * simpl in H8. 
      destruct (Rgt_dec (x_general mal init A (t_eps + 1) i)
                    (A_M - (a * eps_0 - (1 - a) * eps))).
      ++ simpl.
         assert ((x_general mal init A (t_eps + 1) i <= A_M - (a * eps_0 - (1 - a) * eps))%Re).
         { apply (@x_val_decreases_2 i a A_m A_M t_eps 0%N #|Normal_general A| eps eps_0).
           + by [].
           + by [].
           + by [].
           + by [].
           + rewrite cardE. destruct H. by apply size_normal_gt_0.
           + apply ltnW. rewrite cardE. destruct H. by apply size_normal_gt_0.
           + by destruct H9.
           + by [].
           + by [].
           + by [].
           + destruct H9. specialize (H6 i). (*specialize (H6 i H9).*) by destruct H6.
           + destruct H9. specialize (H6 i). (*specialize (H6 i H9). *) by destruct H6.
           + by [].
           + by destruct H9.
           + by rewrite addn0 /eps_j.
         }
         apply Rle_not_gt in H10. contradiction.
      ++ by simpl.
    * by simpl in H8.
Qed.

Lemma X_m_size_decreases_from_0_1 
  (t_eps: nat) (a A_m A_M:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool): 
    F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
   (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta m_general mal init A] A_m ->
   (0 < a)%Re -> (a < 1)%Re ->
   (eps < a ^ #|Normal_general A| / (1 - a ^ #|Normal_general A|) * eps_0)%Re ->
  (forall i:D, (*i \in Normal -> *) 
     (forall k : D,
          k \in incl_neigh_minus_extremes i (x_general mal init A) (t_eps + 0) ->
          (a <= w (t_eps + 0) (i, k))%Re) /\
     (sum_f_R0
        (fun n0 : nat =>
         w (t_eps + 0)
           (i,
           nth i
             (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + 0))
             n0))
        (size (incl_neigh_minus_extremes i (x_general mal init A) (t_eps + 0)) -
         1) = 1%Re)) ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->  
   (exists i:D, i \in (X_m_t_e_i eps_0 A_m t_eps mal init A) /\ i \in Normal_general A /\
                (F + 1 <=
                   #|in_neighbor i
                     :\: X_m_t_e_i (eps_j 0 eps_0 eps a) A_m
                           (t_eps + 0) mal init A|)%N ) -> 
  (#|X_m_t_e_i (eps_j 1 eps_0 eps a) A_m (t_eps + 1) mal init A
   :&: Normal_general A| <
   #|X_m_t_e_i (eps_j 0 eps_0 eps a) A_m t_eps mal init A
     :&: Normal_general A|)%N.
Proof.
intros.
apply proper_card. rewrite /proper. apply /andP.
split.
+ apply /subsetP. rewrite /sub_mem //=. move => i H9.
  rewrite in_setI in H9. rewrite in_setI. apply /andP.
  assert ( (i \in X_m_t_e_i (a * eps_0 - (1 - a) * eps)
             A_m (t_eps + 1) mal init A) /\ (i \in Normal_general A)).
  { by apply /andP. } destruct H10 as [H10 H11].
  split.
  - rewrite inE. rewrite inE in H10.
    destruct (Rlt_dec (x_general mal init A (t_eps + 1) i)
                (A_m + (a * eps_0 - (1 - a) * eps))).
    * simpl in H10. 
      destruct (Rlt_dec (x_general mal init A t_eps i) (A_m + eps_0)).
      ++ by simpl.
      ++ simpl. apply Rnot_lt_ge in n.
         assert (( x_general mal init A (t_eps + 1) i >= A_m + (a * eps_0 - (1 - a) * eps))%Re).
         { apply (@x_val_increases_1 i a A_m A_M t_eps 0%N #|Normal_general A| eps eps_0).
           + by [].
           + by [].
           + by [].
           + by [].
           + rewrite cardE. destruct H. by apply size_normal_gt_0.
           + apply ltnW. rewrite cardE. destruct H. by apply size_normal_gt_0.
           + by [].
           + by [].
           + by [].
           + by [].
           + specialize (H6 i). (*specialize (H6 i H11). *) by destruct H6.
           + specialize (H6 i). (*specialize (H6 i H11). *) by destruct H6.
           + by [].
           + by rewrite addn0 /eps_j.
         }
         apply Rge_not_lt in H12.
         contradiction.
    * by simpl in H10. 
  - apply H11.
+ apply /subsetPn. rewrite /eps_j. destruct H8 as [i H8].
  exists i. 
  - rewrite in_setI. apply /andP. destruct H8. destruct H9. by split.
  - destruct H8 as [H8 H9].
    rewrite in_setI. apply /nandP. left.
    rewrite inE. rewrite inE in H8.
    destruct (Rlt_dec (x_general mal init A t_eps i) (A_m + eps_0)).
    * simpl in H8. 
      destruct (Rlt_dec (x_general mal init A (t_eps + 1) i)
                    (A_m + (a * eps_0 - (1 - a) * eps))).
      ++ simpl.
         assert ((x_general mal init A (t_eps + 1) i >= A_m + (a * eps_0 - (1 - a) * eps))%Re).
         { apply (@x_val_increases_2 i a A_m A_M t_eps 0%N #|Normal_general A| eps eps_0).
           + by [].
           + by [].
           + by [].
           + by [].
           + rewrite cardE. destruct H. by apply size_normal_gt_0.
           + apply ltnW. rewrite cardE. destruct H. by apply size_normal_gt_0.
           + by destruct H9.
           + by [].
           + by [].
           + by [].
           + destruct H9. specialize (H6 i). (* specialize (H6 i H9). *) by destruct H6.
           + destruct H9. specialize (H6 i). (*specialize (H6 i H9). *) by destruct H6.
           + by [].
           + by destruct H9.
           + by rewrite addn0 /eps_j.
         }
         apply Rge_not_lt in H10. contradiction.
      ++ by simpl.
    * by simpl in H8.
Qed.



Lemma or_tri: forall (P Q R: bool), P || (Q || R) <-> or3 P Q R.
Proof.
intros. split; intros; by apply /or3P.
Qed.


Lemma card_decreases_sym (S1 S2: {set D}): 
  (#|S2| < #|S1|)%N ->
  S2 \subset S1 ->
   (exists i:D, i \in S1 /\ i \notin S2). 
Proof.
intros. assert (S2 \proper S1). { rewrite properEcard. by apply /andP. }
rewrite /proper in H1.
assert ((S2 \subset S1) /\ ~~ (S1 \subset S2)).
{ by apply /andP. } destruct H2.
assert (exists2 i:D, i \in S1 & i \notin S2).
{ by apply /subsetPn. }
destruct H4 as [i H4]. by exists i.
Qed.



Lemma sum_eq: forall (a b c d:nat),
  (a + b + c + d)%N = (a+c+b+d)%N.
Proof.
intros. rewrite -addnA.
rewrite -[in RHS]addnA.
assert ((a + b + (c + d))%N = (a + (b + (c + d)))%N ).
{ by rewrite -addnA. } rewrite H.
assert ((a + c + (b + d))%N = (a + (c + (b + d)))%N).
{ by rewrite -addnA. } rewrite H0.
assert (((b + (c + d)))%N = ((c + (b + d)))%N).
{ rewrite -[in RHS]addnC. rewrite -[in RHS]addnA.
  assert (((c + d))%N = ((d + c))%N).
  { by rewrite addnC. }
  by rewrite H1.
} by rewrite H1.
Qed.

Lemma and_false: forall (A B: bool), 
  (A /\ ~~B) -> A && B = false.
Proof.
intros. destruct H. apply ssrbool.negbTE.
apply /nandP. by right.
Qed.
 
Lemma and_distr: forall (a b c d:bool),
  [&& a && b, c & d] = [&& a && c, b & d].
Proof.
intros. 
destruct a.
+ simpl. destruct b.
  - by [].
  - simpl. by destruct c.
+ by [].
Qed.

Lemma implies_simp: forall (P Q:bool),
  (P -> Q) -> (~~P \/ Q).
Proof.
intros. destruct P.
+ right. by apply H.
+ by left. 
Qed.

Lemma adversary_not_normal_lem (A: D -> bool):
  Adversary_general A = ~: Normal_general A.
Proof.
rewrite -setTD. apply eq_finset. unfold eqfun. move =>i.
rewrite !inE.
by destruct (A i == true).
Qed.

Lemma adversary_max: forall (A B: {set D}) (P : D -> bool),
  F_totally_bounded_general P ->
  A :&: B = set0 ->
  (#|A :\: Normal_general P| + #|B :\: Normal_general P| <=F)%N.
Proof.
intros. rewrite -cardsUI. rewrite -setDIl.
rewrite H0 set0D cards0 addn0 -setDUl.
apply leq_trans with #|Adversary_general P|.
+ apply subset_leqif_cards. 
  assert (Adversary_general P = ~: Normal_general P).
  { apply adversary_not_normal_lem. } 
  rewrite -setTD in H1. rewrite H1.
  apply setSD. apply subsetT.
+ rewrite /F_totally_bounded_general in H. rewrite /F_total in H.
  destruct H. by [].
Qed. 


(** Since there are atleast (F+1) nodes in the union, there exists a 
  normal node  in the union with atleadt (F+1) neighbors outside the set
**)
Lemma normal_node_cond (t_eps: nat) (A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_totally_bounded_general  A ->
  (A_M - eps_0 > A_m + eps_0)%Re ->
  (F + 1 <=
     #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
         (F + 1)| +
     #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
         (F + 1) |)%N ->
  exists i:D, (i \in X_M_t_e_i eps_0 A_M t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N) \/
               (i \in X_m_t_e_i eps_0 A_m t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N).
Proof.
intros.
assert ( #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)|  = 
           (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1) :&: Normal_general A | +
             #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1) :\: Normal_general A|)%N).
{ by rewrite cardsID. }
assert ( #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)| = 
        (#|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1) :&: Normal_general A | +
             #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1) :\: Normal_general A|)%N).
{ by rewrite cardsID. }
rewrite H2 H3 in H1.
assert ((#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)
           :&: Normal_general A| +
         #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)
           :\: Normal_general A| +
         (#|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
            :&: Normal_general A| +
          #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
            :\: Normal_general A|))%N = 
      ((#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)
           :&: Normal_general A| + #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
            :&: Normal_general A|) + 
      ( #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)
           :\: Normal_general A| + #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
            :\: Normal_general A|))%N).
{ rewrite !addnA. by rewrite sum_eq. } rewrite H4 in H1. clear H4.
apply (@add_max_bound (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)
       :&: Normal_general A| +
     #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
       :&: Normal_general A|)%N   (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)
        :\: Normal_general A| +
      #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
        :\: Normal_general A|)%N F) in H1.
+ assert (exists i:D, 
          i \in ((Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)
       :&: Normal_general A) :|:
      (Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
       :&: Normal_general A))).
  { apply /card_gt0P. rewrite cardsU.
    assert ((#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1) :&: Normal_general A
               :&: (Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)
                    :&: Normal_general A)|)%N = 0%N).
    { rewrite setIACA. rewrite setIid.
      apply /eqP. rewrite cards_eq0. apply /eqP. apply eq_finset.
      unfold eqfun. move=>i. apply ssrbool.negbTE.
      apply /nandP. left. rewrite inE. 
      rewrite inE.
      assert ((i \in Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)) = 
                ((i \in X_m_t_e_i eps_0 A_m t_eps mal init A) && 
                  (F + 1 <=
                    #|in_neighbor i :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N)).
      { by rewrite inE. } rewrite H4.
      rewrite and_distr. apply /nandP. left.
      apply /nandP.
      assert ([disjoint (X_M_t_e_i eps_0 A_M t_eps mal init A) & (X_m_t_e_i eps_0 A_m t_eps mal init A)]).
      { by apply X_M_X_m_disjoint. }
      apply (@implies_simp (i \in (X_M_t_e_i eps_0 A_M t_eps mal init A))
                (i \notin X_m_t_e_i eps_0 A_m t_eps mal init A)).
      intros.
      assert ((i \in (X_m_t_e_i eps_0 A_m t_eps mal init A) = false) ->
             i \notin (X_m_t_e_i eps_0 A_m t_eps mal init A)). 
      { intros. by apply ssrbool.negbT. }
      apply H7. 
      by apply (@disjointFr D (X_M_t_e_i eps_0 A_M t_eps mal init A) (X_m_t_e_i eps_0 A_m t_eps mal init A) i). 
    } by rewrite H4 subn0.
  } destruct H4 as [ i H4].
  exists i.
  assert ( i \in (Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
                    (F + 1) :&: Normal_general A) \/ 
           i \in (Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
                    (F + 1) :&: Normal_general A)).
  { apply /orP. by rewrite -in_setU. }
  destruct H5.
  - left.
    rewrite inE in H5.
    assert ((i \in Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
              (F + 1)) /\ (i \in Normal_general A)).
    { by apply /andP. } destruct H6 as [H6 H7].
    rewrite inE in H6.
    assert ((i \in X_M_t_e_i eps_0 A_M t_eps mal init A) /\
               (F + 1 <=
                #|in_neighbor i :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N).
    { by apply /andP. } destruct H8 as [H8 H9].
    split.
    * by []. (*rewrite in_setU. apply /orP. left. apply H8. *)
    * split.
      ++ apply H7.
      ++ (*left. *) apply H9.
  - right. rewrite inE in H5.
    assert ((i \in Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
              (F + 1)) /\ (i \in Normal_general A)).
    { by apply /andP. } destruct H6 as [H6 H7].
    rewrite inE in H6.
    assert ((i \in X_m_t_e_i eps_0 A_m t_eps mal init A) /\
             (F + 1 <=
              #|in_neighbor i :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N).
    { by apply /andP. } destruct H8 as [H8 H9].
    split.
    * (*rewrite in_setU. apply /orP. by right.*) by [].
    * split.
      ++ apply H7.
      ++ (*by right. *) by [].
+ apply adversary_max.
  - by [].
  - apply eq_finset. unfold eqfun. move=>i.
    rewrite inE. 
    assert (i \in Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1) = 
              ((i \in X_m_t_e_i eps_0 A_m t_eps mal init A) && 
                (F + 1 <=
                  #|in_neighbor i :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N)).
    { by rewrite inE. } rewrite H4. rewrite and_distr.
    apply ssrbool.negbTE. apply /nandP. left.
    apply /nandP. apply implies_simp.
    intros. apply ssrbool.negbT.
    apply (@disjointFr D (X_M_t_e_i eps_0 A_M t_eps mal init A) (X_m_t_e_i eps_0 A_m t_eps mal init A) i).
    * by apply X_M_X_m_disjoint.
    * by []. 
Qed.


Lemma split_ineq: forall (a b c:nat),
  (a <= b <= c)%N -> (a <= b)%N /\ (b <= c)%N.
Proof.
intros. by apply /andP. 
Qed.

Lemma and_tri_simp: forall (a b:bool),
  a && b && a = a && b.
Proof.
intros. destruct a.
+ simpl. destruct b. 
  - by [].
  - by [].
+ by [].
Qed.


Lemma P_implies_and: forall (P : bool),
  P -> (P && true).
Proof.
intros. by destruct P.
Qed.


Lemma X_M_card_gt_0 (t_eps: nat) (A_M: R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool): 
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init  ->
   (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta M_general mal init A] A_M -> 
  (0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N.
Proof.
intros. rewrite card_gt0. apply /set0Pn.
assert ( exists i:D, i \in (X_M_t_e_i eps_0 A_M t_eps mal init A) /\ i \in Normal_general A).
{ by apply X_M_normal_exists. } destruct H3 as [i H3].
exists i. by destruct H3.
Qed.

Lemma X_m_card_gt_0 (t_eps: nat) (A_m: R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool) : 
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta m_general mal init A] A_m -> 
  (0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N.
Proof.
intros. rewrite card_gt0. apply /set0Pn.
assert ( exists i:D, i \in (X_m_t_e_i eps_0 A_m t_eps mal init A) /\ i \in Normal_general A).
{ by apply X_m_normal_exists. } destruct H3 as [i H3].
exists i. by destruct H3.
Qed.


Lemma normal_node_cond1_implies (t_eps: nat) (A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init: D -> R) (A : D -> bool):
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta M_general mal init A] A_M -> 
  #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)| ==
     #|X_M_t_e_i eps_0 A_M t_eps mal init A| ->
  exists i:D, (i \in X_M_t_e_i eps_0 A_M t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N) \/
               (i \in X_m_t_e_i eps_0 A_m t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N).
Proof.
intros.
assert ( exists i:D, i \in (X_M_t_e_i eps_0 A_M t_eps mal init A) /\
                        i \in Normal_general A).
{ by apply X_M_normal_exists. }
destruct H4 as [i H4]. destruct H4 as [H4 H5].
exists i. left. split.
+ by []. 
+ split.
  - apply H5.
  - rewrite eqn_leq in H3. apply split_ineq in H3.
    destruct H3 as [H3 H6].
    assert ((Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)) \subset 
              (X_M_t_e_i eps_0 A_M t_eps mal init A)).
    { apply /setIidPl. apply eq_finset. unfold eqfun. move => j.
      rewrite inE. by rewrite and_tri_simp.
    } 
    assert ((Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1) \subset
               X_M_t_e_i eps_0 A_M t_eps mal init A) &&  
            ((#|X_M_t_e_i eps_0 A_M t_eps mal init A| <=
                #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)|)%N)).
    { apply /andP. by split. }
    assert (Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1) == 
                  X_M_t_e_i eps_0 A_M t_eps mal init A).
    { by rewrite eqEcard. }
    rewrite eqEsubset in H9.
    assert ((Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1) \subset
                  X_M_t_e_i eps_0 A_M t_eps mal init A) /\
                 (X_M_t_e_i eps_0 A_M t_eps mal init A\subset
                  Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1))).
    { by apply /andP. } destruct H10 as [H10 H11].
    rewrite subsets_disjoint in H11.
    apply (@disjointFr D (X_M_t_e_i eps_0 A_M t_eps mal init A)
              (~: (Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1))) i) in H11.
    * rewrite in_setC in H11. apply ssrbool.negbT in H11. rewrite inE in H11.
      assert (((i \in X_M_t_e_i eps_0 A_M t_eps mal init A) &&
                 (F + 1 <=
                  #|in_neighbor i
                    :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N)).
      { by apply /negPn. }
      assert ((i \in X_M_t_e_i eps_0 A_M t_eps mal init A) /\
                (F + 1 <=
                 #|in_neighbor i :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N).
      { by apply /andP. } by destruct H13.
    * by [].
Qed.


Lemma normal_node_cond2_implies (t_eps: nat) (A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
   (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta m_general mal init A] A_m -> 
  #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)| ==
     #|X_m_t_e_i eps_0 A_m t_eps mal init A| ->
  exists i:D, (i \in X_M_t_e_i eps_0 A_M t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N) \/
               (i \in X_m_t_e_i eps_0 A_m t_eps  mal init A/\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N).
Proof.
intros.
assert ( exists i:D, i \in (X_m_t_e_i eps_0 A_m t_eps mal init A) /\
                        i \in Normal_general A).
{ by apply X_m_normal_exists. }
destruct H4 as [i H4]. destruct H4 as [H4 H5].
exists i. right. split.
+ by []. 
+ split.
  - apply H5.
  - rewrite eqn_leq in H3. apply split_ineq in H3.
    destruct H3 as [H3 H6].
    assert ((Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)) \subset 
              (X_m_t_e_i eps_0 A_m t_eps mal init A)).
    { apply /setIidPl. apply eq_finset. unfold eqfun. move => j.
      rewrite inE. by rewrite and_tri_simp.
    } 
    assert ((Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1) \subset
               X_m_t_e_i eps_0 A_m t_eps mal init A) && 
            ((#|X_m_t_e_i eps_0 A_m t_eps mal init A| <=
                #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)|)%N)).
    { apply /andP. by split. }
    assert (Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1) == 
                  X_m_t_e_i eps_0 A_m t_eps mal init A).
    { by rewrite eqEcard. }
    rewrite eqEsubset in H9.
    assert ((Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1) \subset
                  X_m_t_e_i eps_0 A_m t_eps mal init A) /\
                 (X_m_t_e_i eps_0 A_m t_eps mal init A \subset
                  Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1))).
    { by apply /andP. } destruct H10 as [H10 H11].
    rewrite subsets_disjoint in H11.
    apply (@disjointFr D (X_m_t_e_i eps_0 A_m t_eps mal init A)
              (~: (Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1))) i) in H11.
    * rewrite in_setC in H11. apply ssrbool.negbT in H11. rewrite inE in H11.
      assert (((i \in X_m_t_e_i eps_0 A_m t_eps mal init A) &&
                 (F + 1 <=
                  #|in_neighbor i
                    :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N)).
      { by apply /negPn. }
      assert ((i \in X_m_t_e_i eps_0 A_m t_eps mal init A) /\
                (F + 1 <=
                 #|in_neighbor i :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N).
      { by apply /andP. } by destruct H13.
    * by [].
Qed.



Lemma r_s_robustness_cond_implies
  (t_eps: nat) (A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta m_general mal init A] A_m -> 
  is_lim_seq [eta M_general mal init A] A_M ->
  (A_M - eps_0 > A_m + eps_0)%Re ->
  [|| #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
             (F + 1)| ==
         #|X_M_t_e_i eps_0 A_M t_eps mal init A|,
         #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
             (F + 1)| ==
         #|X_m_t_e_i eps_0 A_m t_eps mal init A|
       | (F + 1 <=
          #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
              (F + 1)| +
          #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
              (F + 1)|)%N] ->
      exists i:D, (i \in X_M_t_e_i eps_0 A_M t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N) \/
               (i \in X_m_t_e_i eps_0 A_m t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N).
Proof.
intros.
apply or_tri in H5. destruct H5.
+ by apply normal_node_cond1_implies.
+ by apply normal_node_cond2_implies.
+ rewrite /F_total_malicious_general in H. destruct H. 
  by apply normal_node_cond.
Qed.



Lemma exists_at_jp1_implies_at_j (t_eps j N: nat) (a A_m A_M :R) (eps eps_0: posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
   (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta M_general mal init A] A_M ->
  (0 < N)%N -> (0 < j)%N -> (j <= N)%N ->
  (0 < a)%Re ->
  (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (forall i:D, (*i \in Normal ->  *)
    let incl :=
         incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)
         in
       (forall k : D,
        k \in incl ->
        (a <= w (t_eps + j) (i, k))%Re) /\
       sum_f_R0
         (fun n : nat =>
          w (t_eps + j) (i, nth i incl n))
         (size incl - 1) = 1%Re) -> 
  (forall t : nat,
        (t >= t_eps)%coq_nat ->
        (m_general mal init A t > A_m - eps)%Re /\
        (M_general mal init A t < A_M + eps)%Re) ->
   (0 <
       #|X_M_t_e_i (eps_j j.+1 eps_0 eps a) A_M
           (t_eps + j.+1) mal init A:&: Normal_general A|)%N ->
  (0 < #|X_M_t_e_i (eps_j j eps_0 eps a)
                             A_M (t_eps + j) mal init A :&: Normal_general A|)%N.
Proof.
intros.
rewrite card_gt0. rewrite card_gt0 in H11.
apply /set0Pn.
assert ( exists x : D,
            x
              \in X_M_t_e_i (eps_j j.+1 eps_0 eps a) A_M
                    (t_eps + j.+1) mal init A :&: Normal_general A).
{ by apply /set0Pn. } destruct H12 as [i H12].
exists i.
rewrite inE. rewrite inE in H12.
assert ((i \in X_M_t_e_i (eps_j j.+1 eps_0 eps a) A_M
              (t_eps + j.+1) mal init A) /\ (i \in Normal_general A)).
{ by apply /andP. } destruct H13.
apply /andP. split.
+ rewrite inE. rewrite inE in H13.
  destruct (Rgt_dec (x_general mal init A (t_eps + j.+1) i)
                (A_M - eps_j j.+1 eps_0 eps a)).
  - simpl in H13.
    destruct (Rgt_dec (x_general mal init A (t_eps + j) i)
                  (A_M - eps_j j eps_0 eps a)).
    * by simpl.
    * simpl. apply Rnot_gt_le in n.
      assert ((x_general mal init A (t_eps + j.+1) i <=
                  A_M - eps_j j.+1 eps_0 eps a)%Re).
      { apply (@x_val_decreases_1 i a A_m A_M t_eps j N eps eps_0).
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + specialize (H9 i). (*specialize (H9 i H14). *) by destruct H9.
        + specialize (H9 i). (*specialize (H9 i H14). *) by destruct H9.
        + by [].
        + by [].
      } apply Rle_not_gt in H15. contradiction.
  - by simpl in H13.
+ by [].
Qed.
 
Lemma exists_at_jp1_implies_at_j_m (t_eps j N: nat) (a A_m A_M:R) (eps eps_0: posreal)
  (mal: nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta m_general mal init A] A_m ->
  (0 < N)%N -> (0 < j)%N -> (j <= N)%N ->
  (0 < a)%Re ->
  (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (forall i:D, (*i \in Normal -> *)
    let incl :=
         incl_neigh_minus_extremes i (x_general mal init A) (t_eps + j)
         in
       (forall k : D,
        k \in incl ->
        (a <= w (t_eps + j) (i, k))%Re) /\
       sum_f_R0
         (fun n : nat =>
          w (t_eps + j) (i, nth i incl n))
         (size incl - 1) = 1%Re) -> 
  (forall t : nat,
        (t >= t_eps)%coq_nat ->
        (m_general mal init A t > A_m - eps)%Re /\
        (M_general mal init A t < A_M + eps)%Re) ->
   (0 <
       #|X_m_t_e_i (eps_j j.+1 eps_0 eps a) A_m
           (t_eps + j.+1) mal init A :&: Normal_general A|)%N ->
  (0 < #|X_m_t_e_i (eps_j j eps_0 eps a)
                             A_m (t_eps + j) mal init A :&: Normal_general A|)%N.
Proof.
intros.
rewrite card_gt0. rewrite card_gt0 in H11.
apply /set0Pn.
assert ( exists x : D,
            x
              \in X_m_t_e_i (eps_j j.+1 eps_0 eps a) A_m
                    (t_eps + j.+1) mal init A :&: Normal_general A).
{ by apply /set0Pn. } destruct H12 as [i H12].
exists i.
rewrite inE. rewrite inE in H12.
assert ((i \in X_m_t_e_i (eps_j j.+1 eps_0 eps a) A_m
              (t_eps + j.+1) mal init A) /\ (i \in Normal_general A)).
{ by apply /andP. } destruct H13.
apply /andP. split.
+ rewrite inE. rewrite inE in H13.
  destruct (Rlt_dec (x_general mal init A (t_eps + j.+1) i)
                (A_m + eps_j j.+1 eps_0 eps a)).
  - simpl in H13.
    destruct (Rlt_dec (x_general mal init A (t_eps + j) i)
                  (A_m + eps_j j eps_0 eps a)).
    * by simpl.
    * simpl. apply Rnot_lt_ge in n.
      assert ((x_general mal init A (t_eps + j.+1) i >=
                  A_m + eps_j j.+1 eps_0 eps a)%Re).
      { apply (@x_val_increases_1 i a A_m A_M t_eps j N eps eps_0).
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + by [].
        + specialize (H9 i). (*specialize (H9 i H14).*) by destruct H9.
        + specialize (H9 i). (*specialize (H9 i H14). *)by destruct H9.
        + by [].
        + by [].
    } apply Rge_not_lt in H15. contradiction.
  - by simpl in H13.
+ by [].
Qed. 


Lemma ltn_addl: forall (a b c d:nat),
  (a <= c)%N -> (b < d)%N ->
  (a + b < c +d)%N.
Proof.
intros. apply leq_ltn_trans with (c+b)%N.
+ by rewrite leq_add2r.
+ by rewrite ltn_add2l.
Qed.

Lemma ltn_addr: forall (a b c d:nat),
  (a < c)%N -> (b <= d)%N ->
  (a + b < c +d)%N.
Proof.
intros. apply ltn_leq_trans with (c+b)%N.
+ by rewrite ltn_add2r.
+ by rewrite leq_add2l.
Qed.


Lemma sj_ind_var (s1 s2: nat -> nat) (N:nat):
  (0< N)%N -> (s1 1%N  + s2 1%N < N)%N  -> 
  (forall j:nat, (0 <j)%N -> (j <= N)%N ->
      (0< s1 j)%N -> (0 < s2 j)%N ->
      (s1 j <= s1 j.-1)%N /\ (s2 j <= s2 j.-1)%N /\
      (( s1 j < s1 j.-1 )%N \/ (s2 j < s2 j.-1)%N)) ->
  exists T:nat, (T<=N)%N /\ (s1 T = 0%N \/ s2 T = 0%N).
Proof.
intros.
assert ( forall j:nat, (0<j)%N -> (j <= N)%N -> 
            s1 j = 0%N \/ s2 j = 0%N \/ 
                (s1 j + s2 j <= s1 1%N + s2 1%N  - (j.-1))%N).
{ intros. induction j.
  + by [].
  + assert (j = 0%N \/ (0<j)%N). 
    { assert ((0<=j)%N). { by []. } rewrite leq_eqVlt in H4.
      assert ((0%N == j) \/ (0 < j)%N). { by apply /orP.  }
      destruct H5.
      + left. rewrite eq_sym in H5. by apply /eqP.
      + by right.
    } destruct H4.
    - rewrite H4 //=. right. right. by rewrite subn0.
    - specialize (H1 j.+1 H2 H3). 
      assert (s1 j.+1 = 0%N \/ (0 < s1 j.+1)%N). 
      { assert ((0<=s1 j.+1)%N). { by []. } rewrite leq_eqVlt in H5.
        assert ((0%N == s1 j.+1) \/ (0 < s1 j.+1)%N). { by apply /orP.  }
        destruct H6.
        + left. rewrite eq_sym in H6. by apply /eqP.
        + by right.
      } destruct H5.
      * by left.
      * specialize (H1 H5).
        assert (s2 j.+1 = 0%N \/ (0 < s2 j.+1)%N). 
        { assert ((0<=s2 j.+1)%N). { by []. } rewrite leq_eqVlt in H6.
          assert ((0%N == s2 j.+1) \/ (0 < s2 j.+1)%N). { by apply /orP.  }
          destruct H7.
          + left. rewrite eq_sym in H7. by apply /eqP.
          + by right.
        } destruct H6.
        ++ right. by left.
        ++ specialize (H1 H6).
           assert ((j <= N)%N). { by apply ltnW in H3. }
           specialize (IHj H4 H7). simpl. simpl in H1.
           destruct H1. destruct H8.
           destruct IHj.
           + rewrite H10 in H1. left. rewrite leqn0 in H1.
             by apply /eqP.
           + destruct H10.
             - rewrite H10 in H8. right. left. rewrite leqn0 in H8.
               by apply /eqP.
             - assert ((s1 j.+1 + s2 j.+1 < (s1 j + s2 j))%N).
               {  destruct H9.
                  + by apply ltn_addr. 
                  + by apply ltn_addl. 
               } 
               rewrite leq_eqVlt in H10.
               assert (((s1 j + s2 j)%N == (s1 1+ s2 1 - j.-1)%N) \/ (s1 j + s2 j < s1 1 + s2 1 - j.-1)%N).
               { by apply /orP. } destruct H12.
               - assert ((s1 j  + s2 j)%N = (s1 1 + s2 1 - j.-1)%N). { by apply /eqP. }
                 rewrite H13 in H11. 
                 assert ((0 <= s1 1 + s2 1 - j.-1)%N). { by []. }
                 rewrite leq_eqVlt in H14.
                 assert ((0%N == (s1 1 + s2 1 - j.-1)%N)
                           \/ (0 < s1 1 + s2 1 - j.-1)%N).
                 { by apply /orP. } destruct H15.
                 * assert ((s1 1 + s2 1 - j.-1)%N = 0%N).
                   { rewrite eq_sym in H15. by apply /eqP. }
                   rewrite H16 in H11.
                   by rewrite ltn0 in H11.
                 * right. right.
                   assert ((s1 1 + s2 1 - j)%N = (s1 1 + s2 1 - j.-1.+1)%N).
                   { by rewrite prednK.  } rewrite H16.
                   rewrite subnS. apply ltnSE. rewrite prednK.
                   ++ by [].
                   ++ by [].
               - right. right. 
                 assert ((0 <= s1 1 + s2 1 - j.-1)%N). { by []. }
                 rewrite leq_eqVlt in H13.
                 assert ((0%N == (s1 1 + s2 1 - j.-1)%N)
                           \/ (0 < s1 1 + s2 1 - j.-1)%N).
                 { by apply /orP. } destruct H14.
                 * assert ((s1 1 + s2 1 - j.-1)%N = 0%N).
                   { rewrite eq_sym in H14. by apply /eqP. }
                   rewrite H15 in H12.
                   by rewrite ltn0 in H12.
                 * assert ((s1 1 + s2 1 - j)%N = (s1 1 + s2 1 - j.-1.+1)%N).
                   { by rewrite prednK.  } rewrite H15.
                   rewrite subnS. apply ltnSE. rewrite prednK.
                   ++ by apply ltn_trans with (s1 j + s2 j)%N.
                   ++ by [].
}
exists N. split.
+ by [].
+ specialize (H2 N H).
  assert ((N<=N)%N). { by []. } specialize (H2 H3).
  destruct H2.
  - by left.
  - destruct H2.
    * by right.
    * assert ((s1 N + s2 N)%N = 0%N).
      { assert ((s1 N + s2 N < 1)%N -> (s1 N + s2 N)%N = 0%N).
        { intros. apply ltnSE in H4. rewrite leqn0 in H4.
          by apply /eqP.
        } apply H4.
        apply leq_ltn_trans with (s1 1%N + s2 1%N - (N.-1))%N.
        + by [].
        + rewrite ltn_psubLR.
          - rewrite addn1. by rewrite prednK.
          - by [].
      } 
      assert (s1 N = 0%N /\ s2 N = 0%N).
      { assert ((s1 N == 0%N) && (s2 N == 0%N)).
        { rewrite  -addn_eq0. by apply /eqP. }
        assert ((s1 N == 0%N) /\ (s2 N == 0%N)).
        { by apply /andP. }
        destruct H6. split.
        + by apply /eqP.
        + by apply /eqP.
      } destruct H5. by left.
Qed.



Lemma max_bound_var (A_M:R) (t:nat) (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_totally_bounded_general A ->
  (0 < F + 1 <= #|D|)%N ->
  (forall (i:D), 
    i \in Normal_general A -> (x_general mal init A t i < A_M)%Re) ->
   (M_general mal init A t < A_M)%Re.
Proof.
intros. 
rewrite /M_general. apply bigmax_lt.
+ rewrite size_map. by apply size_normal_gt_0.
+ intros. rewrite size_map in H2.
  specialize (H1 (nth key (enum (Normal_general A)) i)).
  assert (nth key (enum (Normal_general A)) i \in Normal_general A ).
  { by apply nth_normal. } specialize (H1 H3).
  assert (x_general mal init A t (nth key (enum (Normal_general A)) i) = 
          [seq x_general mal init A t i | i <- enum (Normal_general A)]`_i ).
  { assert ( [seq x_general mal init A t i | i <- enum (Normal_general A)]`_i = 
                 (fun i:D => (x_general mal init A t i)) (nth key (enum (Normal_general A)) i)).
    { by apply nth_map. } by rewrite H4.
  } rewrite -H4. by apply H1.
Qed.

Lemma min_bound_var (A_m:R) (t: nat)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_totally_bounded_general A  ->
  (0 < F + 1 <= #|D|)%N ->
  (forall (i:D), 
    i \in Normal_general A -> (x_general mal init A t i > A_m)%Re) ->
   (m_general mal init A t > A_m)%Re.
Proof.
intros.
rewrite /m_general. 
assert (A_m = (- - A_m)%Re). { by rewrite Ropp_involutive. }
rewrite H2. apply Ropp_lt_gt_contravar.
apply bigmax_lt.
+ rewrite size_map. by apply size_normal_gt_0.
+ intros. rewrite size_map in H3.
  specialize (H1 (nth key (enum (Normal_general A)) i)).
  assert (nth key (enum (Normal_general A)) i \in Normal_general A ).
  { by apply nth_normal. } specialize (H1 H4).
  assert (- x_general mal init A t (nth key (enum (Normal_general A)) i) = 
          [seq - (x_general mal init A t i) | i <- enum (Normal_general A)]`_i ).
  { assert ( [seq - (x_general mal init A t i) | i <- enum (Normal_general A)]`_i = 
                 (fun i:D => - (x_general mal init A t i)) (nth key (enum (Normal_general A)) i)).
    { by apply (@nth_map D key R 0%Re (fun i:D => - (x_general mal init A t i)) i (enum (Normal_general A))) . }
    by rewrite H5.
  } rewrite -H5. by apply Ropp_gt_lt_contravar , H1.
Qed.



Lemma X_M_card_le (t_eps j N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init  ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta M_general mal init A] A_M ->
  (0 < N)%N -> (0<j)%N -> (j<=N)%N ->
  (0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (forall (i:D)(t:nat), (*i \in Normal -> *)
          let incl := incl_neigh_minus_extremes i (x_general mal init A) t in
              (forall k : D,
                        k \in incl ->
                        (a <= w t (i, k))%Re) /\
                       sum_f_R0
                         (fun n : nat =>
                          w t (i, nth i incl n))
                         (size incl - 1) = 1%Re) ->
  (#|X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A
   :&: Normal_general A| <=
 #|X_M_t_e_i (eps_j j.-1 eps_0 eps a) A_M (t_eps + j.-1) mal init A
   :&: Normal_general A|)%N.
Proof.
intros.
apply subset_leq_card. apply /subsetP.
rewrite /sub_mem //=. move => k H11.
rewrite in_setI in H11. 
assert ((k \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) /\
          (k \in Normal_general A)).
{ by apply /andP. } destruct H12.
rewrite in_setI. apply /andP. split.
+ rewrite inE in H12. rewrite inE.
  destruct (Rgt_dec (x_general mal init A (t_eps + j) k) (A_M - eps_j j eps_0 eps a)).
  - simpl.
    destruct (Rgt_dec (x_general mal init A (t_eps + j.-1) k) (A_M - eps_j j.-1 eps_0 eps a)).
    * by simpl.
    * simpl. apply Rnot_gt_le in n.
      assert ((x_general mal init A (t_eps + j) k <= A_M - eps_j j eps_0 eps a)%Re).
      { assert (j = (j-1).+1). { rewrite subn1. by rewrite prednK. }
        rewrite H14.
        apply x_val_decreases_1 with A_m N.
        - by [].
        - by [].
        - by [].
        - by [].
        - by [].
        - apply leq_trans with j.
          ++ rewrite subn1. apply leq_pred.
          ++ by [].
        - by [].
        - by [].
        - by [].
        - by [].
        - specialize (H10 k (t_eps + (j-1))%N). (*specialize (H10 k (t_eps + (j-1))%N H13). *) by destruct H10.
        - specialize (H10 k (t_eps + (j-1))%N). (*specialize (H10 k (t_eps + (j-1))%N H13).  *)by destruct H10.
        - by [].
        - by rewrite subn1.
      } apply Rle_not_gt in H14.
      contradiction.
  - by simpl in H12.
+ by [].
Qed.

Lemma X_m_card_le (t_eps j N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A : D -> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta m_general mal init A] A_m ->
  (0 < N)%N -> (0<j)%N -> (j<=N)%N ->
  (0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (forall (i:D)(t:nat), (*i \in Normal -> *)
          let incl := incl_neigh_minus_extremes i (x_general mal init A) t in
              (forall k : D,
                        k \in incl ->
                        (a <= w t (i, k))%Re) /\
                       sum_f_R0
                         (fun n : nat =>
                          w t (i, nth i incl n))
                         (size incl - 1) = 1%Re) ->
  (#|X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A
   :&: Normal_general A| <=
 #|X_m_t_e_i (eps_j j.-1 eps_0 eps a) A_m (t_eps + j.-1) mal init A
   :&: Normal_general A|)%N.
Proof.
intros.
apply subset_leq_card. apply /subsetP.
rewrite /sub_mem //=. move => k H11.
rewrite in_setI in H11. 
assert ((k \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A) /\
          (k \in Normal_general A)).
{ by apply /andP. } destruct H12.
rewrite in_setI. apply /andP. split.
+ rewrite inE in H12. rewrite inE.
  destruct (Rlt_dec (x_general mal init A (t_eps + j) k) (A_m + eps_j j eps_0 eps a)).
  - simpl.
    destruct (Rlt_dec (x_general mal init A (t_eps + j.-1) k) (A_m + eps_j j.-1 eps_0 eps a)).
    * by simpl.
    * simpl. apply Rnot_gt_le in n.
      assert ((x_general mal init A(t_eps + j) k >= A_m + eps_j j eps_0 eps a)%Re).
      { assert (j = (j-1).+1). { rewrite subn1. by rewrite prednK. }
        rewrite H14.
        apply x_val_increases_1 with A_M N.
        - by [].
        - by [].
        - by [].
        - by [].
        - by [].
        - apply leq_trans with j.
          ++ rewrite subn1. apply leq_pred.
          ++ by [].
        - by [].
        - by [].
        - by [].
        - by [].
        - specialize (H10 k (t_eps + (j-1))%N). (*specialize (H10 k (t_eps + (j-1))%N H13). *)by destruct H10.
        - specialize (H10 k (t_eps + (j-1))%N). (*specialize (H10 k (t_eps + (j-1))%N H13). *)by destruct H10.
        - by [].
        - rewrite subn1. by apply Rle_ge.
      } apply Rge_not_lt in H14.
      contradiction.
  - by simpl in H12.
+ by [].
Qed.


Lemma X_M_X_m_lt_bound (t_eps N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init ->
    (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta M_general mal init A] A_M ->
  is_lim_seq [eta m_general mal init A] A_m ->
  (0 < N)%N -> 
  (0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (forall (i:D)(t:nat), (*i \in Normal -> *)
          let incl := incl_neigh_minus_extremes i (x_general mal init A) t in
              (forall k : D,
                        k \in incl ->
                        (a <= w t (i, k))%Re) /\
                       sum_f_R0
                         (fun n : nat =>
                          w t (i, nth i incl n))
                         (size incl - 1) = 1%Re) ->
  (exists i:D, (i \in X_M_t_e_i eps_0 A_M t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N) \/
               (i \in X_m_t_e_i eps_0 A_m t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N)) ->
  (#|X_M_t_e_i (eps_j 0 eps_0 eps a) A_M (t_eps + 0) mal init A
   :&: Normal_general A| +
 #|X_m_t_e_i (eps_j 0 eps_0 eps a) A_m (t_eps + 0) mal init A
   :&: Normal_general A| <= N)%N ->
  (#|X_M_t_e_i (eps_j 1 eps_0 eps a) A_M (t_eps + 1) mal init A
   :&: Normal_general A| +
 #|X_m_t_e_i (eps_j 1 eps_0 eps a) A_m (t_eps + 1) mal init A
   :&: Normal_general A| < N)%N.
Proof.
intros.
destruct H10 as [i H10]. destruct H10. 
+ destruct H10. destruct H12.
  apply ltn_leq_trans with 
  (#|X_M_t_e_i (eps_j 0 eps_0 eps a) A_M (t_eps + 0) mal init A
     :&: Normal_general A| +
   #|X_m_t_e_i (eps_j 1 eps_0 eps a) A_m (t_eps + 1) mal init A
     :&: Normal_general A|)%N.
  - rewrite ltn_add2r. apply card_decreases. exists i.
    split.
    * rewrite in_setI //=. apply /andP. rewrite addn0. by split.
    * rewrite inE. apply /nandP. left. rewrite inE.
      rewrite inE in H10.
      destruct (Rgt_dec (x_general mal init A t_eps i) (A_M - eps_0)).
      ++ simpl in H11.
         destruct (Rgt_dec (x_general mal init A (t_eps + 1) i) (A_M - eps_j 1 eps_0 eps a)).
         + simpl.
           assert ((x_general mal init A (t_eps + 1) i <=  A_M - eps_j 1 eps_0 eps a)%Re).
           { apply x_val_decreases_2 with A_m N.
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + specialize (H9 i (t_eps+0)%N). (*specialize (H9 i (t_eps+0)%N H12). *) by destruct H9.
             + specialize (H9 i (t_eps+0)%N). (*specialize (H9 i (t_eps+0)%N H12). *) by destruct H9.
             + by [].
             + rewrite addn0 //=.
             + rewrite addn0 //=.
           } apply Rle_not_gt in H14.
           contradiction.
         + by simpl.
      ++ by simpl in H10.
    * apply /subsetP. rewrite /sub_mem //=. move=> p H14.
         rewrite in_setI in H14.
         assert ((p \in X_M_t_e_i (a * eps_j 0 eps_0 eps a - (1 - a) * eps) A_M
                            (t_eps + 1) mal init A) /\ (p \in Normal_general A)).
         { simpl. by apply /andP. } destruct H15.
         rewrite in_setI. apply /andP. split.
         * rewrite inE. rewrite inE in H15.
           rewrite addn0.
           destruct (Rgt_dec (x_general mal init A (t_eps + 1) p)
                          (A_M - (a * eps_j 0 eps_0 eps a  - (1 - a) * eps))).
           ++ simpl in H15.
              destruct (Rgt_dec (x_general mal init A (t_eps) p)
                                (A_M - eps_0 )).
              - by simpl. 
              - simpl. intros. apply Rnot_gt_le in n.
                assert ((x_general mal init A (t_eps + 1) p <= A_M -
                                  (a * eps_j 0 eps_0 eps a - (1 - a) * eps))%Re).
                { apply x_val_decreases_1 with A_m N.
                  + by [].
                  + by []. (*rewrite /wts_well_behaved. exists a. by split. *)
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + specialize (H9 p (t_eps+0)%N). (*specialize (H9 p (t_eps+0)%N H16). *) by destruct H9. 
                  + specialize (H9 p (t_eps+0)%N). (*specialize (H9 p (t_eps+0)%N H16). *) by destruct H9. 
                  + by [].
                  + rewrite addn0 //=. 
                 } apply Rle_not_gt in H17.
                 contradiction.
             ++ by simpl in H15. 
          * by [].
    - apply leq_trans with 
       (#|X_M_t_e_i (eps_j 0 eps_0 eps a) A_M (t_eps + 0) mal init A
         :&: Normal_general A| +
       #|X_m_t_e_i (eps_j 0 eps_0 eps a) A_m (t_eps + 0) mal init A
         :&: Normal_general A|)%N.
      * rewrite leq_add2l. 
        assert (0%N = 1.-1). { by []. } rewrite H14.
        assert (1.-1.+1 = 1%N). { by []. } rewrite H15.
        by apply (@X_m_card_le t_eps 1%N N a A_M A_m eps_0 eps).
      * by [].
+ destruct H10. destruct H12.
  apply ltn_leq_trans with 
  (#|X_M_t_e_i (eps_j 1 eps_0 eps a) A_M (t_eps + 1) mal init A
     :&: Normal_general A| +
   #|X_m_t_e_i (eps_j 0 eps_0 eps a) A_m (t_eps + 0) mal init A
     :&: Normal_general A|)%N.
  - rewrite ltn_add2l. apply card_decreases. exists i.
    split.
    * rewrite in_setI //=. apply /andP. rewrite addn0. by split.
    * rewrite inE. apply /nandP. left. rewrite inE.
      rewrite inE in H10.
      destruct (Rlt_dec (x_general mal init A t_eps i) (A_m +eps_0)).
      ++ simpl in H10.
         destruct (Rlt_dec (x_general mal init A (t_eps + 1) i) (A_m + eps_j 1 eps_0 eps a)).
         + simpl. 
           assert ((x_general mal init A (t_eps + 1) i >=  A_m + eps_j 1 eps_0 eps a)%Re).
           { apply x_val_increases_2 with A_M N.
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + by [].
             + specialize (H9 i (t_eps+0)%N). (*specialize (H9 i (t_eps+0)%N H12). *)by destruct H9.
             + specialize (H9 i (t_eps+0)%N). (*specialize (H9 i (t_eps+0)%N H12). *)by destruct H9.
             + by [].
             + rewrite addn0 //=.
             + rewrite addn0 //=.
           } apply Rge_not_lt in H14.
           contradiction.
         + by simpl.
      ++ by simpl in H10.
    * apply /subsetP. rewrite /sub_mem //=. move=> p H14.
         rewrite in_setI in H14.
         assert ((p \in X_m_t_e_i (a * eps_j 0 eps_0 eps a - (1 - a) * eps) A_m
                            (t_eps + 1) mal init A) /\ (p \in Normal_general A)).
         { simpl. by apply /andP. } destruct H15.
         rewrite in_setI. apply /andP. split.
         * rewrite inE. rewrite inE in H15.
           rewrite addn0.
           destruct (Rlt_dec (x_general mal init A (t_eps + 1) p)
                          (A_m + (a * eps_j 0 eps_0 eps a  - (1 - a) * eps))).
           ++ simpl in H15.
              destruct (Rlt_dec (x_general mal init A (t_eps) p)
                                (A_m + eps_0 )).
              - by simpl. 
              - simpl. intros. apply Rnot_gt_le in n.
                assert ((x_general mal init A (t_eps + 1) p >= A_m +
                                  (a * eps_j 0 eps_0 eps a - (1 - a) * eps))%Re).
                { apply x_val_increases_1 with A_M N.
                  + by [].
                  + by []. (*rewrite /wts_well_behaved. exists a. by split. *)
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + specialize (H9 p (t_eps+0)%N). (*specialize (H9 p (t_eps+0)%N H16). *) by destruct H9. 
                  + specialize (H9 p (t_eps+0)%N). (*specialize (H9 p (t_eps+0)%N H16). *) by destruct H9. 
                  + by [].
                  + rewrite addn0 //=. by apply Rle_ge. 
                 } apply Rge_not_lt in H17.
                 contradiction.
             ++ by simpl in H15. 
          * by [].
    - apply leq_trans with 
       (#|X_M_t_e_i (eps_j 0 eps_0 eps a) A_M (t_eps + 0) mal init A
         :&: Normal_general A| +
       #|X_m_t_e_i (eps_j 0 eps_0 eps a) A_m (t_eps + 0) mal init A
         :&: Normal_general A|)%N.
      * rewrite leq_add2r. 
        assert (0%N = 1.-1). { by []. } rewrite H14.
        assert (1.-1.+1 = 1%N). { by []. } rewrite H15.
        by apply (@X_M_card_le t_eps 1%N N a A_M A_m eps_0 eps).
      * by [].
Qed.
    

Lemma X_M_X_m_sum_at_0_le_N (t_eps N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init  ->
  is_lim_seq [eta M_general mal init A] A_M ->
  is_lim_seq [eta m_general mal init A] A_m ->
  (0 < N)%N -> 
  (0 < a)%Re -> (a < 1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
  (A_M - eps_0 > A_m + eps_0)%Re ->
  (forall (i:D)(t:nat), (*i \in Normal -> *) 
          let incl := incl_neigh_minus_extremes i (x_general mal init A) t in
              (forall k : D,
                        k \in incl ->
                        (a <= w t (i, k))%Re) /\
                       sum_f_R0
                         (fun n : nat =>
                          w t (i, nth i incl n))
                         (size incl - 1) = 1%Re) ->
  (#|X_M_t_e_i (eps_j 0 eps_0 eps a) A_M (t_eps + 0) mal init A
     :&: Normal_general A| +
   #|X_m_t_e_i (eps_j 0 eps_0 eps a) A_m (t_eps + 0) mal init A
     :&: Normal_general A| <= #|Normal_general A|)%N.
Proof.
intros.
rewrite -cardsUI.
assert (#|X_M_t_e_i (eps_j 0 eps_0 eps a) A_M (t_eps + 0) mal init A
         :&: Normal_general A
         :&: (X_m_t_e_i (eps_j 0 eps_0 eps a) A_m (t_eps + 0) mal init A
              :&: Normal_general A)| = 0%N).
{ rewrite -setIACA setIid.
  assert (X_M_t_e_i (eps_j 0 eps_0 eps a) A_M (t_eps + 0) mal init A
            :&: X_m_t_e_i (eps_j 0 eps_0 eps a) A_m (t_eps + 0) mal init A = set0).
  { apply /eqP. rewrite setI_eq0.
    by apply X_M_X_m_disjoint.
  } rewrite H10.
  rewrite set0I. by rewrite cards0.
}
rewrite H10. rewrite addn0.
rewrite -setIUl. apply bound_intersect.
Qed.


Lemma normal_bound_exists 
  (t_eps: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init  ->
    (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta m_general mal init A] A_m -> 
  is_lim_seq [eta M_general mal init A] A_M ->
  (1 < #|D|)%N  ->
  (A_M - eps_0 > A_m + eps_0)%Re ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
   (0<a)%Re -> (a < 1)%Re ->
    let N:= #|Normal_general A| in 
   (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
   (forall (i:D)(t:nat), (*i \in Normal -> *) 
          let incl := incl_neigh_minus_extremes i (x_general mal init A) t in
              (forall k : D,
                        k \in incl ->
                        (a <= w t (i, k))%Re) /\
                       sum_f_R0
                         (fun n : nat =>
                          w t (i, nth i incl n))
                         (size incl - 1) = 1%Re) ->
    (exists i : D,
      i \in X_M_t_e_i eps_0 A_M t_eps mal init A /\
      i \in Normal_general A /\
      (F + 1 <= #|in_neighbor i :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N \/
      i \in X_m_t_e_i eps_0 A_m t_eps  mal init A /\
      i \in Normal_general A /\
      (F + 1 <= #|in_neighbor i :\: X_m_t_e_i eps_0 A_m t_eps mal init A|)%N) ->
     (forall j:nat, (0<j)%N -> (j<=N)%N ->
                (eps_j j eps_0 eps a < eps_j (j-1)%N eps_0 eps a)%Re ->   
                 ( ( (0 < #|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N) mal init A :&: Normal_general A|)%N ->
                      (#|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N) mal init A :&: Normal_general A| <
                  #| (X_M_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_M (t_eps+(j-1))%N) mal init A :&: Normal_general A|)%N) \/
                  ( (0 < #|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N) mal init A :&: Normal_general A|)%N ->
                    (#|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N) mal init  A :&: Normal_general A| <
                      #| (X_m_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_m (t_eps+(j-1))%N) mal init A :&: Normal_general A|)%N))) ->
    (exists t : nat, (M_general mal init A t < A_M)%Re \/ (m_general mal init A t > A_m)%Re).
Proof.
intros.
assert (exists T:nat,(T<=N)%N /\ 
          (#|(X_M_t_e_i (eps_j T eps_0 eps a) A_M (t_eps + T)%N) mal init A :&: Normal_general A| = 0%N \/
           #|(X_m_t_e_i (eps_j T eps_0 eps a) A_m (t_eps + T)%N) mal init A :&: Normal_general A| = 0%N)).
{ apply sj_ind_var.
  + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
  + apply X_M_X_m_lt_bound.
    - by [].
    - by [].
    - by [].
    - by [].
    - by [].
    - rewrite /N cardE. destruct H. by apply size_normal_gt_0.
    - by [].
    - by [].
    - by [].
    - by [].
    - by [].
    - by [].
    - apply X_M_X_m_sum_at_0_le_N with N.
      * by [].
      * by [].
      * by [].
      * by [].
      * rewrite /N cardE. destruct H. by apply size_normal_gt_0.
      * by [].
      * by [].
      * by [].
      * by [].
      * by [].
      * by [].
  + intros. specialize (H12 j H13 H14).
    assert ((eps_j j eps_0 eps a <
                  eps_j (j - 1) eps_0 eps a)%Re).
    { apply eps_j_lt_j_minus_1 with A .
      + by destruct H. 
      + by [].
      + by destruct H.
      + by [].
      + by [].
      + by [].
      + by [].
      + by rewrite -/N.
      + by [].
    } specialize (H12 H17). split.
    - apply X_M_card_le with N A_m.
      * by [].
      * by [].
      * by [].
      * by [].
      * rewrite /N cardE. destruct H. by apply size_normal_gt_0.
      * by [].
      * by [].
      * by [].
      * by [].
      * by [].
      * by [].
      * by [].
    - split.
      * apply X_m_card_le with N A_M.
        ++ by [].
        ++ by [].
        ++ by [].
        ++ by [].
        ++ rewrite /N cardE. destruct H. by apply size_normal_gt_0.
        ++ by [].
        ++ by [].
        ++ by [].
        ++ by [].
        ++ by [].
        ++ by [].
        ++ by [].  
      * destruct H12.
        ++ left. rewrite -subn1. by specialize (H12 H15).
        ++ right. rewrite -subn1. by specialize (H12 H16).
}
destruct H13 as [T H13]. destruct H13.
exists (t_eps+T)%N. destruct H14.
+ left. apply cards0_eq in H14.
  assert (X_M_t_e_i (eps_j T eps_0 eps a) A_M
            (t_eps + T)  mal init A :&: Normal_general A == set0).
  { by apply /eqP. } rewrite setI_eq0 in H15.
  assert ((forall i : D, i \in Normal_general A -> (x_general mal init A (t_eps+T)%N i < A_M)%Re) -> 
              (M_general mal init A (t_eps + T) < A_M)%Re).
  { destruct H. by apply max_bound_var. } apply H16. intros. 
  assert ([disjoint
          X_M_t_e_i (eps_j T eps_0 eps a) A_M
            (t_eps + T)  mal init A & Normal_general A] ->
           i \in Normal_general A ->
           i \notin (X_M_t_e_i (eps_j T eps_0 eps a) A_M (t_eps + T) mal init A )).
  { intros. 
    assert ((i \in (X_M_t_e_i (eps_j T eps_0 eps a) A_M (t_eps + T) mal init A ) = false) ->
               i \notin (X_M_t_e_i (eps_j T eps_0 eps a) A_M (t_eps + T) mal init A )). 
    { intros. by apply ssrbool.negbT. } 
    apply H20. move: H18 H19. apply disjointFl.
  } specialize (H18 H15 H17).
  rewrite inE in H18.
  destruct (Rgt_dec (x_general mal init A (t_eps + T) i)
         (A_M - eps_j T eps_0 eps a)).
  + by simpl in H18. 
  + intros. simpl in H18. apply Rnot_gt_le in n.
    apply Rle_lt_trans with (A_M - eps_j T eps_0 eps a)%Re.
    - apply n.
    - assert ( (0 < eps_j T eps_0 eps a )%Re).
      { apply eps_j_gt_0 with N.
        + rewrite /N cardE. destruct H. by apply size_normal_gt_0.
        + by [].
        + by [].
        + by [].
      } nra.
+ right. apply cards0_eq in H14.
  assert (X_m_t_e_i (eps_j T eps_0 eps a) A_m
            (t_eps + T) mal init A :&: Normal_general A == set0).
  { by apply /eqP. } rewrite setI_eq0 in H15.
  assert ((forall i : D, i \in Normal_general A -> (x_general mal init A (t_eps+T)%N i > A_m)%Re) -> 
              (m_general mal init A (t_eps + T) > A_m)%Re).
  { destruct H. by apply min_bound_var. } apply H16. intros. 
  assert ([disjoint
          X_m_t_e_i (eps_j T eps_0 eps a) A_m
            (t_eps + T) mal init A & Normal_general A] ->
           i \in Normal_general A ->
           i \notin (X_m_t_e_i (eps_j T eps_0 eps a) A_m (t_eps + T) mal init A )).
  { intros. 
    assert ((i \in (X_m_t_e_i (eps_j T eps_0 eps a) A_m (t_eps + T) mal init A ) = false) ->
               i \notin (X_m_t_e_i (eps_j T eps_0 eps a) A_m (t_eps + T) mal init A )). 
    { intros. by apply ssrbool.negbT. } 
    apply H20. move: H18 H19. apply disjointFl.
  } specialize (H18 H15 H17).
  rewrite inE in H18.
  destruct (Rlt_dec (x_general mal init A (t_eps + T) i)
         (A_m + eps_j T eps_0 eps a)).
  + by simpl in H18. 
  + intros. simpl in H18. apply Rnot_gt_le in n.
    apply Rlt_le_trans with (A_m + eps_j T eps_0 eps a)%Re.
    - assert ( (0 < eps_j T eps_0 eps a )%Re).
      { apply eps_j_gt_0 with N.
        + rewrite /N cardE. destruct H. by apply size_normal_gt_0.
        + by [].
        + by [].
        + by [].
      } nra.
    - apply n.
Qed.

Lemma X_M_normal_exists_at_j (t_eps j N: nat) (a A_M: R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool): 
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init  ->
    (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta M_general mal init A] A_M ->
    (0 < N)%N ->(j<=N)%N -> (0 < a < 1)%Re ->
    (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
    exists i:D, i \in (X_M_t_e_i (eps_j j eps_0 eps a) A_M
                (t_eps + j) mal init A ) /\ i \in Normal_general A.
Proof.
intros. 
assert (M_general mal init A (t_eps+j) \in map (fun i:D => x_general mal init A  (t_eps +j) i) (enum (Normal_general A))).
{ rewrite /M_general . 
  apply (@bigmaxr_mem _ 0%Re (map (fun i:D => x_general mal init A (t_eps+j) i) (enum (Normal_general A)))).
  rewrite size_map. destruct H. by apply size_normal_gt_0.
} 
assert (exists2 i:D, i \in (enum (Normal_general A)) &
            (M_general mal init A (t_eps+j) = (fun i:D => x_general mal init A (t_eps+j) i) i)).
{ by apply /mapP. }
destruct H8 as [i H8]. exists i.
split.
+ rewrite inE. rewrite -H9.
  destruct (Rgt_dec (M_general mal init A (t_eps+j)) (A_M - eps_j j eps_0 eps a)).
  - by simpl.
  - simpl.  
    assert ((A_M - eps_j j eps_0 eps a < M_general mal init A (t_eps+j))%Re).
    { apply Rlt_le_trans with (A_M - 0)%Re.
      + apply Rplus_lt_compat_l. apply Ropp_gt_lt_contravar.
        by apply eps_j_gt_0 with N.
      + assert ((A_M - 0)%Re = A_M). { nra. }
        rewrite H10. by apply M_A_M_lower_bound.
    } apply Rlt_gt in H10.
    contradiction.
+ by apply in_enum_Normal.
Qed. 

Lemma X_m_normal_exists_at_j (t_eps j N: nat) (a A_m: R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool): 
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init  ->
     (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta m_general mal init A] A_m ->
    (0 < N)%N ->(j<=N)%N -> (0 < a < 1)%Re ->
    (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
    exists i:D, i \in (X_m_t_e_i (eps_j j eps_0 eps a) A_m
                (t_eps + j) mal init A) /\ i \in Normal_general A.
Proof.
intros. 
assert ((-(m_general mal init A (t_eps+j))) \in map (fun i:D => - x_general mal init A (t_eps+j) i) (enum (Normal_general A))).
{ rewrite /m_general. rewrite -RoppE. rewrite Ropp_involutive.
  apply (@bigmaxr_mem _ 0%Re (map (fun i:D => - x_general mal init A (t_eps+j) i) (enum (Normal_general A)))).
  rewrite size_map. destruct H. by apply size_normal_gt_0.
} 
assert (exists2 i:D, i \in (enum (Normal_general A)) &
            (- (m_general mal init A (t_eps+j)) = (fun i:D => - x_general mal init A (t_eps+j) i) i)).
{ by apply /mapP. }
destruct H8 as [i H8]. exists i.
split.
+ rewrite inE.
  assert (m_general mal init A (t_eps +j)= x_general mal init A (t_eps +j) i). 
  { rewrite -[LHS]Ropp_involutive. rewrite !RoppE. rewrite H9.
    by rewrite -!RoppE Ropp_involutive.
  } rewrite -H10.
  destruct (Rlt_dec (m_general mal init A (t_eps+j)) (A_m + eps_j j eps_0 eps a)).
  - by simpl.
  - simpl. 
    assert ((m_general mal init A (t_eps +j)  < A_m + eps_j j eps_0 eps a)%Re).
    { apply Rle_lt_trans with (A_m + 0)%Re.
      + assert ((A_m + 0)%Re = A_m). { nra. }
        rewrite H11. by apply m_A_m_lower_bound.
      + apply Rplus_lt_compat_l. 
        by apply eps_j_gt_0 with N.
    }
    contradiction.
+ by apply in_enum_Normal.
Qed.


Lemma X_M_X_m_disjoint_at_j (mal : nat -> D ->R) (init: D -> R) (A: D -> bool):
  forall (t_eps j:nat) (a A_M A_m :R) (eps_0 eps :posreal),
  (A_M - (eps_j j eps_0 eps a) > A_m + (eps_j j eps_0 eps a))%Re ->
  [disjoint (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) & 
    (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A )].
Proof.
intros. rewrite -setI_eq0. apply /eqP.
apply eq_finset. unfold eqfun. move=>i.
rewrite /X_M_t_e_i /X_m_t_e_i.
rewrite !in_set. apply /andP. 
apply /andP. apply /nandP.
destruct (Rgt_dec (x_general mal init A (t_eps+j) i) (A_M - (eps_j j eps_0 eps a))).
+ simpl. 
  destruct (Rlt_dec (x_general mal init A (t_eps+j) i) (A_m + (eps_j j eps_0 eps a))).
  - simpl. left.
    assert ((x_general mal init A (t_eps+j) i > A_m + (eps_j j eps_0 eps a))%Re).
    { apply Rgt_trans with (A_M - (eps_j j eps_0 eps a))%Re; by []. }
    assert ((x_general mal init A (t_eps+j) i > A_m + (eps_j j eps_0 eps a))%Re -> 
            ~(x_general mal init A (t_eps+j) i < A_m + (eps_j j eps_0 eps a))%Re). { nra. }
    specialize (H1 H0).
    contradiction.
  - simpl. by right.
+ simpl. by left.
Qed.


Lemma X_M_mem_j (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  forall (t_eps j:nat) (a A_M A_m :R) (eps_0 eps:posreal),
  (0 < #|D|)%N ->  (A_M - eps_j  j eps_0 eps a > A_m + eps_j j eps_0 eps a )%Re -> 
  (0 < #|(X_m_t_e_i (eps_j j eps_0 eps a) A_m
                (t_eps + j) mal init A)|)%N -> 
  (X_M_t_e_i (eps_j j eps_0 eps a) A_M
                (t_eps + j) mal init A) \proper Vertex.
Proof.
intros.
rewrite properEcard.
apply /andP. split.
- apply subsetT.
- rewrite cardsCs.
  assert (#|[set: D]| = #|D|).
  { by rewrite cardsT. } rewrite H2.
  rewrite ltn_subrL. apply /andP. split.
  * rewrite card_gt0. apply /set0Pn.
    exists (nth key (enum (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)) 0%N).
    rewrite inE -disjoints1.
    apply single_element_disjoint.
    ++ by [].
    ++ rewrite disjoint_sym.
       by apply X_M_X_m_disjoint_at_j.
  * apply H.
Qed.


Lemma X_m_mem_j (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
  forall (t_eps j:nat) (a A_M A_m :R) (eps_0 eps:posreal),
  (0 < #|D|)%N ->  (A_M - (eps_j j eps_0 eps a) > A_m + (eps_j j eps_0 eps a))%Re -> 
  (0 < #|X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|)%N -> 
  X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A \proper Vertex.
Proof.
intros.
rewrite properEcard.
apply /andP. split.
- apply subsetT.
- rewrite cardsCs.
  assert (#|[set: D]| = #|D|).
  { by rewrite cardsT. } rewrite H2.
  rewrite ltn_subrL. apply /andP. split.
  * rewrite card_gt0. apply /set0Pn.
    exists (nth key (enum (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)) 0%N).
    rewrite inE -disjoints1.
    apply single_element_disjoint.
    ++ by [].
    ++ by apply (@X_M_X_m_disjoint_at_j mal init A t_eps j a A_M A_m eps_0 eps).
  * apply H.
Qed.


Lemma eps_j_lt_0 (j N: nat) (a:R) (eps eps_0: posreal):
  (0<N)%N -> (0<j)%N -> (j<=N)%N -> (0<a)%Re -> (a <1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (eps_j j eps_0 eps a  < eps_0)%Re.
Proof.
intros. induction j.
+ by [].
+ assert ((0<=j)%N). { by []. } rewrite leq_eqVlt in H5.
  assert ((0%N == j) \/ (0 < j)%N). { by apply /orP. }
  destruct H6.
  - assert (j=0%N). { rewrite eq_sym in H6. by apply /eqP. }
    rewrite H7 //=. apply Rlt_trans with (a*eps_0)%Re.
    * assert ((0<(1 - a) * eps)%Re). 
      { apply Rmult_lt_0_compat.
        + nra.
        + apply posreal_cond.
      } nra.
    * assert ((1 * eps_0)%Re = eps_0). { nra. } rewrite -H8.
      assert ((a * (1 * eps_0))%Re = (a*eps_0)%Re). { nra. }
      rewrite H9. apply Rmult_lt_compat_r.
      ++ apply posreal_cond.
      ++ by [].
  - simpl. specialize (IHj H6). apply ltnW in H1. specialize (IHj H1).
    apply Rlt_trans with (a * eps_j j eps_0 eps a)%Re.
    * assert ((0< (1 - a) * eps)%Re). 
      { apply Rmult_lt_0_compat.
        + nra.
        + apply posreal_cond.
      } nra.
    * assert ((1 * eps_0)%Re = eps_0). { nra. } rewrite -H7.
      apply Rmult_gt_0_lt_compat.
      + by apply eps_j_gt_0 with N.
      + nra.
      + nra.
      + by [].
Qed.
   


(** (A_M - eps_j j eps_0 eps a > A_m + eps_j j eps_0 eps a)%Re **)
Lemma A_M_let_A_m_at_j (t_eps j N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat ->D -> R) (init : D -> R) (A : D -> bool):
  (0<N)%N -> (0<j)%N -> (j<=N)%N -> (0<a)%Re -> (a <1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (A_M - eps_0 > A_m + eps_0)%Re ->
  (A_M - eps_j j eps_0 eps a > A_m + eps_j j eps_0 eps a)%Re.
Proof.
intros.
apply Rlt_trans with (A_m + eps_0)%Re.
+ apply Rplus_lt_compat_l. by apply eps_j_lt_0 with N.
+ apply Rlt_trans with (A_M - eps_0)%Re.
  - by [].
  - apply Rplus_lt_compat_l. by apply Ropp_lt_contravar, eps_j_lt_0 with N. 
Qed.


Lemma normal_node_cond_at_j (t_eps j N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D-> R) (A: D -> bool):
  F_totally_bounded_general A  ->
  (A_M - (eps_j j eps_0 eps a) > A_m + (eps_j j eps_0 eps a))%Re ->
  (0 < N)%N -> (j <= N)%N -> (0<a)%Re -> (a <1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  (F + 1 <=
     #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)
         (F + 1)| +
     #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)
         (F + 1)|)%N ->
  exists i:D, (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|)%N) \/
               (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A  /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A|)%N).
Proof.
intros.
assert ( #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)|  = 
           (#|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1) :&: Normal_general A | +
             #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1) :\: Normal_general A|)%N).
{ by rewrite cardsID. }
assert ( #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)| = 
        (#|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1) :&: Normal_general A | +
             #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1) :\: Normal_general A|)%N).
{ by rewrite cardsID. }
rewrite H7 H8 in H6.
assert ((#|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)
           :&: Normal_general A| +
         #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)
           :\: Normal_general A| +
         (#|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)
            :&: Normal_general A| +
          #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)
            :\: Normal_general A|))%N = 
      ((#|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)
           :&: Normal_general A| + #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init  A) (F + 1)
            :&: Normal_general A|) + 
      ( #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)
           :\: Normal_general A| + #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)
            :\: Normal_general A|))%N).
{ rewrite !addnA. by rewrite sum_eq. } rewrite H9 in H6. clear H9.
apply (@add_max_bound (#|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)
       :&: Normal_general A| +
     #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)
       :&: Normal_general A|)%N   (#|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)
        :\: Normal_general A| +
      #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)
        :\: Normal_general A|)%N F) in H6.
+ assert (exists i:D, 
          i \in ((Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)
       :&: Normal_general A) :|:
      (Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)
       :&: Normal_general A))).
  { apply /card_gt0P. rewrite cardsU.
    assert ((#|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1) :&: Normal_general A
               :&: (Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)
                    :&: Normal_general A)|)%N = 0%N).
    { rewrite setIACA. rewrite setIid.
      apply /eqP. rewrite cards_eq0. apply /eqP. apply eq_finset.
      unfold eqfun. move=>i. apply ssrbool.negbTE.
      apply /nandP. left. rewrite inE. 
      rewrite inE.
      assert ((i \in Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)) = 
                ((i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) && 
                  (F + 1 <=
                    #|in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A |)%N)).
      { by rewrite inE. } rewrite H9.
      rewrite and_distr. apply /nandP. left.
      apply /nandP.
      assert ([disjoint (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) & (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)]).
      { by apply X_M_X_m_disjoint_at_j. }
      apply (@implies_simp (i \in (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A))
                (i \notin X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)).
      intros.
      assert ((i \in (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) = false) ->
             i \notin (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)). 
      { intros. by apply ssrbool.negbT. }
      apply H12. 
      by apply (@disjointFr D (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) i). 
    } by rewrite H9 subn0.
  } destruct H9 as [ i H9].
  exists i.
  assert ( i \in (Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)
                    (F + 1) :&: Normal_general A) \/ 
           i \in (Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)
                    (F + 1) :&: Normal_general A)).
  { apply /orP. by rewrite -in_setU. }
  destruct H10.
  - left.
    rewrite inE in H10.
    assert ((i \in Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)
              (F + 1)) /\ (i \in Normal_general A)).
    { by apply /andP. } destruct H11 as [H11 H12].
    rewrite inE in H11.
    assert ((i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) /\
               (F + 1 <=
                #|in_neighbor i :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|)%N).
    { by apply /andP. } destruct H13 as [H13 H14].
    split.
    * by []. (*rewrite in_setU. apply /orP. left. apply H8. *)
    * split.
      ++ apply H12.
      ++ (*left. *) apply H14.
  - right. rewrite inE in H10.
    assert ((i \in Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)
              (F + 1)) /\ (i \in Normal_general A)).
    { by apply /andP. } destruct H11 as [H11 H12].
    rewrite inE in H11.
    assert ((i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A ) /\
             (F + 1 <=
              #|in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A|)%N).
    { by apply /andP. } destruct H13 as [H13 H14].
    split.
    * (*rewrite in_setU. apply /orP. by right.*) by [].
    * split.
      ++ apply H12.
      ++ (*by right. *) by [].
+ apply adversary_max.
  - by [].
  - apply eq_finset. unfold eqfun. move=>i.
    rewrite inE. 
    assert (i \in Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1) = 
              ((i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) && 
                (F + 1 <=
                  #|in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A |)%N)).
    { by rewrite inE. } rewrite H9. rewrite and_distr.
    apply ssrbool.negbTE. apply /nandP. left.
    apply /nandP. apply implies_simp.
    intros. apply ssrbool.negbT.
    apply (@disjointFr D (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) i).
    * by apply X_M_X_m_disjoint_at_j.
    * by []. 
Qed.



Lemma normal_node_cond1_implies_at_j (t_eps j N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init : D -> R) (A: D -> bool):
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init  ->
    (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta M_general mal init A] A_M -> 
   (0 < N)%N -> (j <= N)%N -> (0<a)%Re -> (a <1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
  #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) (F + 1)| ==
     #|X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A| ->
  exists i:D, (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A|)%N) \/
               (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A|)%N).
Proof. 
intros.
assert ( exists i:D, i \in (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) /\
                        i \in Normal_general A).
{  by apply X_M_normal_exists_at_j with N. }
destruct H9 as [i H9]. destruct H9 as [H9 H10].
exists i. left. split.
+ by []. 
+ split.
  - apply H10.
  - rewrite eqn_leq in H8. apply split_ineq in H8.
    destruct H8 as [H8 H11].
    assert ((Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)) \subset 
              (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)).
    { apply /setIidPl. apply eq_finset. unfold eqfun. move => k.
      rewrite inE. by rewrite and_tri_simp.
    } 
    assert ((Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1) \subset
               X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) && 
            ((#|X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A| <=
                #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1)|)%N)).
    { apply /andP. by split. }
    assert (Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1) == 
                  X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A).
    { by rewrite eqEcard. }
    rewrite eqEsubset in H14.
    assert ((Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1) \subset
                  X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) /\
                 (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A \subset
                  Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1))).
    { by apply /andP. } destruct H15 as [H15 H16].
    rewrite subsets_disjoint in H16.
    apply (@disjointFr D (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)
              (~: (Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) (F + 1))) i) in H16.
    * rewrite in_setC in H16. apply ssrbool.negbT in H16. rewrite inE in H16.
      assert (((i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) &&
                 (F + 1 <=
                  #|in_neighbor i
                    :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|)%N)).
      { by apply /negPn. }
      assert ((i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A) /\
                (F + 1 <=
                 #|in_neighbor i :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|)%N).
      { by apply /andP. } by destruct H18.
    * by [].
Qed.


Lemma normal_node_cond2_implies_at_j (t_eps j N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D ->R) (init : D -> R) (A: D -> bool):
   F_total_malicious_general mal init A ->
   wts_well_behaved_general A mal init ->
     (0 < F + 1 <= #|D|)%N ->
   is_lim_seq [eta m_general mal init A] A_m ->
   (0 < N)%N -> (j <= N)%N -> (0<a)%Re -> (a <1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re -> 
  #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)| ==
     #|X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A| ->
  exists i:D, (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|)%N) \/
               (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A|)%N).
Proof.
intros.
assert ( exists i:D, i \in (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) /\
                        i \in Normal_general A).
{ by apply X_m_normal_exists_at_j with N. }
destruct H9 as [i H9]. destruct H9 as [H9 H10].
exists i. right. split.
+ by []. 
+ split.
  - apply H10.
  - rewrite eqn_leq in H8. apply split_ineq in H8.
    destruct H8 as [H8 H11].
    assert ((Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)) \subset 
              (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)).
    { apply /setIidPl. apply eq_finset. unfold eqfun. move => k.
      rewrite inE. by rewrite and_tri_simp.
    } 
    assert ((Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1) \subset
               X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) && 
            ((#|X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A| <=
                #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1)|)%N)).
    { apply /andP. by split. }
    assert (Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1) == 
                  X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A).
    { by rewrite eqEcard. }
    rewrite eqEsubset in H14.
    assert ((Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1) \subset
                  X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) /\
                 (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A \subset
                  Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1))).
    { by apply /andP. } destruct H15 as [H15 H16].
    rewrite subsets_disjoint in H16.
    apply (@disjointFr D (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)
              (~: (Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) (F + 1))) i) in H16.
    * rewrite in_setC in H16. apply ssrbool.negbT in H16. rewrite inE in H16.
      assert (((i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) &&
                 (F + 1 <=
                  #|in_neighbor i
                    :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A|)%N)).
      { by apply /negPn. }
      assert ((i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A) /\
                (F + 1 <=
                 #|in_neighbor i :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A|)%N).
      { by apply /andP. } by destruct H18.
    * by [].
Qed.



Lemma r_s_robustness_cond_implies_at_j
  (t_eps j N: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init: D -> R) (A: D -> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init  ->
  (0 < F + 1 <= #|D|)%N ->
  is_lim_seq [eta m_general mal init A] A_m -> 
  is_lim_seq [eta M_general mal init A] A_M ->
  (0 < N)%N -> (j <= N)%N -> (0<a)%Re -> (a <1)%Re ->
  (eps < a ^ N / (1 - a ^ N) * eps_0)%Re -> 
  (A_M - (eps_j j eps_0 eps a) > A_m + (eps_j j eps_0 eps a))%Re ->
  [|| #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)
             (F + 1)| ==
         #|X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|,
         #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)
             (F + 1)| ==
         #|X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A|
       | (F + 1 <=
          #|Xi_S_r (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A)
              (F + 1)| +
          #|Xi_S_r (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A)
              (F + 1)|)%N] ->
      exists i:D, (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps+j) mal init A|)%N) \/
               (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps+j) mal init A|)%N).
Proof.
intros.
apply or_tri in H10. destruct H10.
+ by apply normal_node_cond1_implies_at_j with N.
+ by apply normal_node_cond2_implies_at_j with N.
+ rewrite /F_total_malicious_general in H. destruct H. 
  by apply normal_node_cond_at_j with N.
Qed.




Lemma r_s_robustness_implies (t_eps: nat) (a A_M A_m:R) (eps_0 eps:posreal)
  (mal : nat -> D -> R) (init: D -> R) (A: D-> bool):
  F_total_malicious_general mal init A ->
  wts_well_behaved_general A mal init  ->
  is_lim_seq [eta m_general mal init A] A_m -> 
  is_lim_seq [eta M_general mal init A] A_M ->
  (1 < #|D|)%N  ->
  (A_M - eps_0 > A_m + eps_0)%Re ->
  r_s_robustness (F+1)%N (F+1)%N ->
  (0 < F + 1 <= #|D|)%N  ->
  (forall t : nat,
    (t >= t_eps)%coq_nat ->
    (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re) ->
   (0<a)%Re -> (a < 1)%Re ->
    let N:= #|Normal_general A| in 
   (eps < a ^ N / (1 - a ^ N) * eps_0)%Re ->
   (forall (i:D)(t:nat), (*i \in Normal -> *)
          let incl := incl_neigh_minus_extremes i (x_general mal init A) t in
              (forall k : D,
                        k \in incl ->
                        (a <= w t (i, k))%Re) /\
                       sum_f_R0
                         (fun n : nat =>
                          w t (i, nth i incl n))
                         (size incl - 1) = 1%Re) ->
  ( X_M_t_e_i eps_0 A_M t_eps mal init A \proper Vertex /\
               (0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N ->
               X_m_t_e_i eps_0 A_m t_eps  mal init A \proper Vertex /\
               (0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N ->
               [disjoint
                  X_M_t_e_i eps_0 A_M t_eps mal init A
                & X_m_t_e_i eps_0 A_m t_eps mal init A] ->
               (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
                    (F + 1)| ==
                #|X_M_t_e_i eps_0 A_M t_eps mal init A|)
               || ((#|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
                       (F + 1)| ==
                   #|X_m_t_e_i eps_0 A_m t_eps mal init A|)
               || (F + 1 <=
                   #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
                       (F + 1)| +
                   #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
                       (F + 1)|)%N ))->
             (forall j:nat, (0<j)%N -> (j<=N)%N ->
                (eps_j j eps_0 eps a < eps_j (j-1)%N eps_0 eps a)%Re ->   
                 ( ( (0 < #|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N mal init A) :&: Normal_general A|)%N ->
                      (#|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N mal init A) :&: Normal_general A| <
                  #| (X_M_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_M (t_eps+(j-1))%N mal init A) :&: Normal_general A|)%N) \/
                  ( (0 < #|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N mal init A) :&: Normal_general A|)%N ->
                    (#|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N mal init A) :&: Normal_general A| <
                      #| (X_m_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_m (t_eps+(j-1))%N mal init A) :&: Normal_general A|)%N))).
Proof.
intros.
assert ((0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N). { by apply X_M_card_gt_0. }
assert ((0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N). { by apply X_m_card_gt_0. }
assert (X_M_t_e_i eps_0 A_M t_eps mal init A \proper Vertex).
{ apply (@X_M_mem mal init A t_eps A_M A_m eps_0).
  + by apply ltn_trans with 1%N.
  + by [].
  + apply H17.
} 
assert (X_M_t_e_i eps_0 A_M t_eps  mal init A \proper Vertex /\
          (0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N).
{ by []. } specialize (H12 H19). clear H19.
assert (X_m_t_e_i eps_0 A_m t_eps mal init A \proper Vertex).
{ apply (@X_m_mem mal init A t_eps A_M A_m eps_0).
  + by apply ltn_trans with 1%N.
  + by []. 
  + apply H16.
}
assert (X_m_t_e_i eps_0 A_m t_eps mal init A \proper Vertex /\
            (0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N).
{ by []. } specialize (H12 H20). clear H20.
assert ([disjoint
           X_M_t_e_i eps_0 A_M t_eps mal init A
         & X_m_t_e_i eps_0 A_m t_eps mal init A]).
{ by apply X_M_X_m_disjoint. }
specialize (H12 H20).

assert (exists i:D, (i \in X_M_t_e_i eps_0 A_M t_eps mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_M_t_e_i eps_0 A_M t_eps mal init A|)%N) \/
               (i \in X_m_t_e_i eps_0 A_m t_eps  mal init A /\ i \in Normal_general A /\
                   (F + 1 <=
                           #|in_neighbor i
                             :\: X_m_t_e_i eps_0 A_m t_eps mal init A |)%N)).
{ by apply r_s_robustness_cond_implies. }
induction j.
+ by [].
+ assert ((0<=j)%N). { by []. } rewrite leq_eqVlt in H22.
  assert ((0%N == j) \/ (0 < j)%N). { by apply /orP. } destruct H23.
  - assert (j=0%N). { rewrite eq_sym in H23. by apply /eqP. }
    rewrite H24. rewrite H24 //= in H13.
    destruct H21 as [i H21]. destruct H21.
    * left. intros. apply card_decreases. exists i. split.
      ++ assert ((1 - 1)%N = 0%N). { by []. } rewrite H26.
         rewrite addn0 //=. rewrite in_setI. apply /andP.
         destruct H21. destruct H27. by split.
      ++ rewrite inE. apply /nandP. left. rewrite inE.
         destruct H21. rewrite inE in H21.
         destruct (Rgt_dec (x_general mal init A t_eps i) (A_M - eps_0)).
         - simpl in H21. destruct H26.
           destruct (Rgt_dec (x_general mal init A (t_eps + 1) i)
                          (A_M - eps_j 1 eps_0 eps a)).
           * simpl.
             assert ((x_general mal init A (t_eps + 1) i <= A_M - eps_j 1 eps_0 eps a)%Re).
             { apply x_val_decreases_2 with A_m N.
               + by [].
               + by []. 
               + by []. 
               + by [].
               + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
               + by [].
               + by [].
               + by [].
               + by [].
               + by [].
               + specialize (H11 i (t_eps+0)%N). (*specialize (H11 i (t_eps+0)%N H26). *) by destruct H11. 
               + specialize (H11 i (t_eps+0)%N). (*specialize (H11 i (t_eps+0)%N H26). *) by destruct H11. 
               + by [].
               + by rewrite addn0. 
               + by rewrite addn0 //=.
             } apply Rgt_not_le in r0. 
             contradiction.
           * by simpl.
         - by simpl in H21.
       ++ apply /subsetP. rewrite /sub_mem //=. move=> p H26.
         rewrite in_setI in H26.
         assert ((p \in X_M_t_e_i (a * eps_j 0 eps_0 eps a - (1 - a) * eps) A_M
                            (t_eps + 1) mal init A) /\ (p \in Normal_general A)).
         { by apply /andP. } destruct H27.
         rewrite in_setI. apply /andP. split.
         * rewrite inE. rewrite inE in H26.
           assert ((1 - 1)%N = 0%N). { by []. } rewrite H29.
           rewrite addn0.
           destruct (Rgt_dec (x_general mal init A (t_eps + 1) p)
                          (A_M - (a * eps_0  - (1 - a) * eps))).
           ++ simpl in H25.
              destruct (Rgt_dec (x_general mal init A (t_eps) p)
                                (A_M - eps_0 )).
              - by simpl. 
              - simpl. intros. apply Rnot_gt_le in n.
                assert ((x_general mal init A (t_eps + 1) p <= A_M -
                                  (a * eps_j 0 eps_0 eps a - (1 - a) * eps))%Re).
                { apply x_val_decreases_1 with A_m N.
                  + by [].
                  + by []. (*rewrite /wts_well_behaved. exists a. by split. *)
                  + by [].
                  + by [].
                  + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + specialize (H11 p (t_eps+0)%N). (*specialize (H11 p (t_eps+0)%N H28). *)by destruct H11. 
                  + specialize (H11 p (t_eps+0)%N). (*specialize (H11 p (t_eps+0)%N H28). *)by destruct H11. 
                  + by [].
                  + by rewrite addn0 //=.
                 } apply Rle_not_gt in H30.
                 contradiction.
             ++ by simpl in H26. 
          * by [].
     * right. intros. apply card_decreases. exists i. split.
      ++ assert ((1 - 1)%N = 0%N). { by []. } rewrite H26.
         rewrite addn0 //=. rewrite in_setI. apply /andP.
         destruct H21. destruct H27. by split.
      ++ rewrite inE. apply /nandP. left. rewrite inE.
         destruct H21. rewrite inE in H21.
         destruct (Rlt_dec (x_general mal init A t_eps i) (A_m + eps_0)).
         - simpl in H21. destruct H26.
           destruct (Rlt_dec (x_general mal init A (t_eps + 1) i)
                          (A_m + eps_j 1 eps_0 eps a)).
           * simpl.
             assert ((x_general mal init A (t_eps + 1) i >= A_m + eps_j 1 eps_0 eps a)%Re).
             { apply x_val_increases_2 with A_M N.
               + by [].
               + by []. 
               + by [].
               + by [].
               + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
               + by [].
               + by [].
               + by [].
               + by [].
               + by [].
               + specialize (H11 i (t_eps+0)%N). (*specialize (H11 i (t_eps+0)%N H26). *)by destruct H11. 
               + specialize (H11 i (t_eps+0)%N). (*specialize (H11 i (t_eps+0)%N H26). *)by destruct H11. 
               + by [].
               + by rewrite addn0. 
               + by rewrite addn0 //=.
             } apply Rlt_not_ge in r0. 
             contradiction.
           * by simpl.
         - by simpl in H21.
       ++ apply /subsetP. rewrite /sub_mem //=. move=> p H26.
         rewrite in_setI in H26.
         assert ((p \in X_m_t_e_i (a * eps_j 0 eps_0 eps a - (1 - a) * eps) A_m
                            (t_eps + 1) mal init A) /\ (p \in Normal_general A)).
         { by apply /andP. } destruct H27.
         rewrite in_setI. apply /andP. split.
         * rewrite inE. rewrite inE in H26.
           assert ((1 - 1)%N = 0%N). { by []. } rewrite H29.
           rewrite addn0.
           destruct (Rlt_dec (x_general mal init A (t_eps + 1) p)
                          (A_m + (a * eps_0  - (1 - a) * eps))).
           ++ simpl in H25.
              destruct (Rlt_dec (x_general mal init A (t_eps) p)
                                (A_m + eps_0 )).
              - by simpl. 
              - simpl. intros. apply Rnot_gt_le in n.
                assert ((x_general mal init A (t_eps + 1) p >= A_m +
                                  (a * eps_j 0 eps_0 eps a - (1 - a) * eps))%Re).
                { apply x_val_increases_1 with A_M N.
                  + by [].
                  + by []. (*rewrite /wts_well_behaved. exists a. by split. *)
                  + by [].
                  + by [].
                  + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + specialize (H11 p (t_eps+0)%N). (*specialize (H11 p (t_eps+0)%N H28). *) by destruct H11. 
                  + specialize (H11 p (t_eps+0)%N). (*specialize (H11 p (t_eps+0)%N H28). *) by destruct H11. 
                  + by [].
                  + rewrite addn0 //=. by apply Rle_ge.
                 } apply Rge_not_lt in H30.
                 contradiction.
             ++ by simpl in H26. 
          * by [].
   - specialize (IHj H23). 
     assert ((eps_j j eps_0 eps a < eps_j (j - 1) eps_0 eps a)%Re).
     { apply eps_j_lt_j_minus_1 with A. 
       + by destruct H.
       + by [].
       + by destruct H.
       + by [].
       + by [].
       + by [].
       + by [].
       + assert ((j<=N)%N \/ (j>=N)%N). { apply /orP. apply leq_total. }
         destruct H24.
         - by rewrite /N in H24.
         - contradict H24. apply /negP. by rewrite -ltnNge.
       + by [].
     } apply ltnW in H14. specialize (IHj H14 H24).
     assert ((0 < #|X_M_t_e_i (eps_j j eps_0 eps a) A_M
                (t_eps + j) mal init A:&: Normal_general A|)%N).
     { apply /card_gt0P. 
       assert (exists i : D, 
                  (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) /\
                  ( i \in Normal_general A)).
        { apply X_M_normal_exists_at_j with N.
          + by [].
          + by [].
          + by [].
          + by [].
          + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
          + by [].
          + by [].
          + by [].
        } destruct H25 as [i H25]. exists i. rewrite in_setI. by apply /andP. 
      }
     assert ((0 < #|X_m_t_e_i (eps_j j eps_0 eps a) A_m
              (t_eps + j) mal init A :&: Normal_general A|)%N ).
     { apply /card_gt0P. 
       assert (exists i : D, 
                  (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A) /\
                  ( i \in Normal_general A)).
        { apply X_m_normal_exists_at_j with N.
          + by [].
          + by [].
          + by [].
          + by [].
          + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
          + by [].
          + by [].
          + by [].
        } destruct H26 as [i H26]. exists i. rewrite in_setI. by apply /andP.
     } 
     rewrite /r_s_robustness in H5.
     destruct H5.
     specialize (H27 H6).
     specialize (H27 (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A)
                     (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A)).
     assert (X_M_t_e_i (eps_j j eps_0 eps a) A_M
                (t_eps + j) mal init A \proper Vertex /\
              (0 <
               #|X_M_t_e_i (eps_j j eps_0 eps a) A_M
                   (t_eps + j) mal init A|)%N).
     { split.
       + apply X_M_mem_j with A_m.
         - by apply ltn_trans with 1%N.
         - apply A_M_let_A_m_at_j with N.
           * by [].
           * by [].
           * by [].
           * by [].
           * rewrite /N cardE. destruct H. by apply size_normal_gt_0.
           * by [].
           * by [].
           * by [].
           * by [].
           * by [].
           * by [].
         - apply /card_gt0P.
           assert ( exists i:D, (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A) /\
                        (i \in Normal_general A)).
           { assert (exists i:D, i \in (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A) :&: Normal_general A).
             { by apply /card_gt0P. } destruct H28 as [k H28].
             exists k. rewrite in_setI in H28. by apply /andP.
           } destruct H28 as [k H28]. destruct H28. by exists k.
         - apply /card_gt0P.
           assert ( exists i:D, (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) /\
                        (i \in Normal_general A)).
           { assert (exists i:D, i \in (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) :&: Normal_general A).
             { by apply /card_gt0P. } destruct H28 as [k H28].
             exists k. rewrite in_setI in H28. by apply /andP.
           } destruct H28 as [k H28]. destruct H28. by exists k.  
     }
     assert (X_m_t_e_i (eps_j j eps_0 eps a) A_m
              (t_eps + j)  mal init A \proper Vertex /\
            (0 <
             #|X_m_t_e_i (eps_j j eps_0 eps a) A_m
                 (t_eps + j) mal init A|)%N).
     { split.
       + apply X_m_mem_j with A_M.
         - by apply ltn_trans with 1%N.
         - apply A_M_let_A_m_at_j with N.
           * by [].
           * by [].
           * by [].
           * by [].
           * rewrite /N cardE. destruct H. by apply size_normal_gt_0.
           * by [].
           * by [].
           * by [].
           * by [].
           * by [].
           * by [].
         - apply /card_gt0P.
           assert ( exists i:D, (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) /\
                        (i \in Normal_general A)).
           { assert (exists i:D, i \in (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A) :&: Normal_general A).
             { by apply /card_gt0P. } destruct H29 as [k H29].
             exists k. rewrite in_setI in H29. by apply /andP.
           } destruct H29 as [k H29]. destruct H29. by exists k.
         - apply /card_gt0P.
           assert ( exists i:D, (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A) /\
                        (i \in Normal_general A)).
           { assert (exists i:D, i \in (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A) :&: Normal_general A).
             { by apply /card_gt0P. } destruct H29 as [k H29].
             exists k. rewrite in_setI in H29. by apply /andP.
           } destruct H29 as [k H29]. destruct H29. by exists k.
     }
     assert ([disjoint
               X_M_t_e_i (eps_j j eps_0 eps a) A_M
                 (t_eps + j) mal init A
             & X_m_t_e_i (eps_j j eps_0 eps a) A_m
                 (t_eps + j) mal init A]).
     { apply X_M_X_m_disjoint_at_j.
       apply A_M_let_A_m_at_j with N.
       * by [].
       * by [].
       * by [].
       * by [].
       * rewrite /N cardE. destruct H. by apply size_normal_gt_0.
       * by [].
       * by [].
       * by [].
       * by [].
       * by [].
       * by [].
     } specialize (H27 H28 H29 H30).
     assert (exists i:D, (i \in X_M_t_e_i (eps_j j eps_0 eps a) A_M
                             (t_eps + j) mal init A /\ i \in Normal_general A /\
                          (F+1 <= #|in_neighbor i
                                     :\: X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A|)%N) \/
                        (i \in X_m_t_e_i (eps_j j eps_0 eps a) A_m
                             (t_eps + j) mal init A /\ i \in Normal_general A /\
                          (F+1 <= #|in_neighbor i
                                     :\: X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A|)%N)).
    { apply r_s_robustness_cond_implies_at_j with N.
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + rewrite /N cardE. destruct H. by apply size_normal_gt_0.
      + by [].
      + by [].
      + by [].
      + by [].
      + apply A_M_let_A_m_at_j with N.
         * by [].
         * by [].
         * by [].
         * by [].
         * rewrite /N cardE. destruct H. by apply size_normal_gt_0.
         * by [].
         * by [].
         * by [].
         * by [].
         * by [].
         * by [].
      + destruct ((#|Xi_S_r
           (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A)
           (F + 1)| ==
       #|X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A|)) eqn:E.
        by [].
        destruct ((#|Xi_S_r
              (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A)
              (F + 1)| ==
          #|X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A|)) eqn:E0.
         by [].
        destruct ((F + 1 <=
          #|Xi_S_r
              (X_M_t_e_i (eps_j j eps_0 eps a) A_M (t_eps + j) mal init A)
              (F + 1)| +
          #|Xi_S_r
              (X_m_t_e_i (eps_j j eps_0 eps a) A_m (t_eps + j) mal init A)
              (F + 1)|)%N) eqn:E1.
        by []. by [].
     } destruct H31 as [k H31]. destruct H31.
    * left. destruct H31. destruct H32.
      assert ( (j.+1 - 1)%N = j). { by rewrite subn1. }
      rewrite H34. intros. apply card_decreases.
      - exists k. split.
        * rewrite in_setI. apply /andP. by split.
        * rewrite inE. apply /nandP. left.
          rewrite inE. rewrite inE in H31.
          destruct (Rgt_dec (x_general mal init A (t_eps + j) k)
                            (A_M - eps_j j eps_0 eps a)).
          ++ simpl in H31. 
             destruct (Rgt_dec (x_general mal init A (t_eps + j.+1) k)
                              (A_M - eps_j j.+1 eps_0 eps a)).
             - simpl. 
               assert ((x_general mal init A (t_eps + j.+1) k <= A_M -
                                  (a * eps_j j eps_0 eps a -(1 - a) * eps))%Re).
               { apply x_val_decreases_2 with A_m N.
                 + by [].
                 + by []. 
                 + by [].
                 + by [].
                 + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
                 + by [].
                 + by [].
                 + by [].
                 + by [].
                 + by [].
                 + specialize (H11 k (t_eps+j)%N). (*specialize (H11 k (t_eps+j)%N H32). *) by destruct H11. 
                 + specialize (H11 k (t_eps+j)%N). (*specialize (H11 k (t_eps+j)%N H32). *) by destruct H11. 
                 + by [].
                 + by [].
                 + by [].
               } apply Rgt_not_le in r0. 
               contradiction.
             - by simpl. 
          ++ by simpl in H31. 
       - apply /subsetP. rewrite /sub_mem //=. move=> p H36.
         rewrite in_setI in H36.
         assert ((p \in X_M_t_e_i (a * eps_j j eps_0 eps a - (1 - a) * eps) A_M
                            (t_eps + j.+1) mal init A) /\ (p \in Normal_general A)).
         { by apply /andP. } destruct H37.
         rewrite in_setI. apply /andP. split.
         * rewrite inE. rewrite inE in H37.
           destruct (Rgt_dec (x_general mal init A (t_eps + j.+1) p)
                          (A_M - (a * eps_j j eps_0 eps a - (1 - a) * eps))).
           ++ simpl in H37.  
              destruct (Rgt_dec (x_general mal init A (t_eps + j) p)
                                (A_M - eps_j j eps_0 eps a)).
              - by simpl. 
              - simpl. intros. apply Rnot_gt_le in n.
                assert ((x_general mal init  A (t_eps + j.+1) p <= A_M -
                                  (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re).
                { apply x_val_decreases_1 with A_m N.
                  + by [].
                  + by []. 
                  + by [].
                  + by [].
                  + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + specialize (H11 p (t_eps+j)%N). (*specialize (H11 p (t_eps+j)%N H38).*) by destruct H11. 
                  + specialize (H11 p (t_eps+j)%N). (*specialize (H11 p (t_eps+j)%N H38). *)by destruct H11. 
                  + by [].
                  + by [].
                 } apply Rle_not_gt in H39.
                 contradiction.
             ++ by simpl in H38. 
          * by [].
     * right. destruct H31. destruct H32.
       assert ( (j.+1 - 1)%N = j). { by rewrite subn1. }
       rewrite H34. intros. apply card_decreases.
       - exists k. split.
        * rewrite in_setI. apply /andP. by split.
        * rewrite inE. apply /nandP. left.
          rewrite inE. rewrite inE in H31.
          destruct (Rlt_dec (x_general mal init A (t_eps + j) k)
                            (A_m + eps_j j eps_0 eps a)).
          ++ simpl in H31. 
             destruct (Rlt_dec (x_general mal init A (t_eps + j.+1) k)
                              (A_m + eps_j j.+1 eps_0 eps a)).
             - simpl. 
               assert ((x_general mal init A  (t_eps + j.+1) k >= A_m +
                                  (a * eps_j j eps_0 eps a -(1 - a) * eps))%Re).
               { apply x_val_increases_2 with A_M N.
                 + by [].
                 + by []. 
                 + by [].
                 + by [].
                 + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
                 + by [].
                 + by [].
                 + by [].
                 + by [].
                 + by [].
                 + specialize (H11 k (t_eps+j)%N). (*specialize (H11 k (t_eps+j)%N H32). *)by destruct H11. 
                 + specialize (H11 k (t_eps+j)%N). (*specialize (H11 k (t_eps+j)%N H32). *) by destruct H11. 
                 + by [].
                 + by [].
                 + by [].
               } apply Rlt_not_ge in r0. 
               contradiction.
             - by simpl. 
          ++ by simpl in H31. 
       - apply /subsetP. rewrite /sub_mem //=. move=> p H36.
         rewrite in_setI in H36.
         assert ((p \in X_m_t_e_i (a * eps_j j eps_0 eps a - (1 - a) * eps) A_m
                            (t_eps + j.+1) mal init A) /\ (p \in Normal_general A)).
         { by apply /andP. } destruct H37.
         rewrite in_setI. apply /andP. split.
         * rewrite inE. rewrite inE in H37.
           destruct (Rlt_dec (x_general mal init A (t_eps + j.+1) p)
                          (A_m + (a * eps_j j eps_0 eps a - (1 - a) * eps))).
           ++ simpl in H37.  
              destruct (Rlt_dec (x_general mal init A (t_eps + j) p)
                                (A_m + eps_j j eps_0 eps a)).
              - by simpl. 
              - simpl. intros. apply Rnot_gt_le in n.
                assert ((x_general mal init A (t_eps + j.+1) p >= A_m +
                                  (a * eps_j j eps_0 eps a - (1 - a) * eps))%Re).
                { apply x_val_increases_1 with A_M N.
                  + by [].
                  + by []. 
                  + by [].
                  + by [].
                  + rewrite /N. rewrite cardE. destruct H. by apply size_normal_gt_0.
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + by [].
                  + specialize (H11 p (t_eps+j)%N). (*specialize (H11 p (t_eps+j)%N H38). *)by destruct H11. 
                  + specialize (H11 p (t_eps+j)%N). (*specialize (H11 p (t_eps+j)%N H38). *)by destruct H11. 
                  + by [].
                  + by apply Rle_ge.
                 } apply Rge_not_lt in H39.
                 contradiction.
             ++ by simpl in H38. 
          * by [].
Qed.
 


Lemma sufficiency_proof:
forall (A:D -> bool) (mal:nat -> D -> R) (init:D -> R),
nonempty_nontrivial_graph ->
(0 < F+1 <= #|D|)%N -> 
wts_well_behaved_general A mal init ->
r_s_robustness (F + 1) (F + 1) ->
Resilient_asymptotic_consensus_general A mal init.
Proof.
intros.
unfold Resilient_asymptotic_consensus_general.
intros.
(*rewrite /F_total_malicious_general in H3. *)
split.
+ assert ((forall t:nat, (M_general mal init A t.+1 <= M_general mal init A t)%Re) -> 
            exists A_M: R, is_lim_seq (fun t: nat => M_general mal init A t) A_M).
  { by apply A_M_exists. }

  assert ((forall t:nat, (m_general mal init A t.+1 >= m_general mal init A t)%Re) -> 
            exists A_m: R, is_lim_seq (fun t: nat => m_general mal init A t) A_m).
  { by apply A_m_exists. } 

  assert (forall t : nat, (M_general mal init A  t.+1 <= M_general mal init A t)%Re).
  { by apply A_M_monotonic. }
  
  assert (forall t:nat, (m_general mal init A t.+1 >= m_general mal init A t)%Re).
  { by apply A_m_monotonic. }

  specialize (H4 H6). specialize (H5 H7).

  destruct H4 as [A_M H4].
  destruct H5 as [A_m H5].

  (** Statement of convergence **)
  assert (forall eps: posreal, exists t_eps: nat,
            forall t:nat, (t >= t_eps)%coq_nat ->
             (m_general mal init A t > A_m - eps)%Re /\ (M_general mal init A t < A_M + eps)%Re).
  { intros. 
    rewrite <-is_lim_seq_spec in H4. rewrite /is_lim_seq' in H4.
    specialize (H4 eps). rewrite /Hierarchy.eventually in H4.
    
    rewrite <-is_lim_seq_spec in H5. rewrite /is_lim_seq' in H5.
    specialize (H5 eps). rewrite /Hierarchy.eventually in H5.
    
    destruct H4 as [N H4]. destruct H5 as [L H5].
    exists (maxn L N).
    intros. specialize (H4 t). specialize (H5 t).
    
    assert ((L <= t)%coq_nat).
    { apply /ssrnat.leP.
      assert ((t >= maxn L N)%N). { by apply /ssrnat.leP. }
      rewrite geq_max in H9. 
      assert ( (L <= t)%N /\ (N <= t)%N). { by apply /andP. }
      by destruct H10.
    } specialize (H5 H9).

    assert ((N <= t)%coq_nat).
    { apply /ssrnat.leP.
      assert ((t >= maxn L N)%N). { by apply /ssrnat.leP. }
      rewrite geq_max in H10. 
      assert ( (L <= t)%N /\ (N <= t)%N). { by apply /andP. }
      by destruct H11.
    } specialize (H4 H10).

    split.
    + apply Rabs_def2 in H5. destruct H5. 
      apply Rlt_gt.
      assert ( m_general mal init A t = (A_m + (m_general mal init A t - A_m))%Re). { nra. }
      rewrite H12. by apply Rplus_lt_compat_l.
    + apply Rabs_def2 in H4. destruct H4. 
      assert ( M_general mal init A t = (A_M + (M_general mal init A t - A_M))%Re). { nra. }
      rewrite H12. by apply Rplus_lt_compat_l.
   }


  assert (forall (A_M A_m:R),
              is_lim_seq (fun t:nat => m_general mal init A t ) A_m ->
              is_lim_seq (fun t:nat => M_general mal init A t) A_M ->
              A_M = A_m -> 
              exists L : Rbar,
                forall i : D,
                i \in Normal_general A -> is_lim_seq ((x_general mal init A)^~ i) L).
  { apply sandwich_x. }
  specialize (H9 A_M A_m H5 H4). apply H9. clear H9.
  symmetry.
  apply P_not_not_P. 
  assert (forall P: Prop, ~P <->  (P -> False)). 
  { intros. by unfold not. } apply H9.
  intros.
  
   assert (forall (A_M : R),
              F_total_malicious_general mal init A ->
              wts_well_behaved_general A mal init  ->
                (0 < F + 1 <= #|D|)%N ->
              is_lim_seq (fun t:nat => M_general mal init A t) A_M ->
              forall t:nat, (A_M <= M_general mal init A t)%Re).
   { by apply M_A_M_lower_bound. } 
   specialize (H11 A_M H3 H1 H0).
   specialize (H11 H4).

   assert (forall (A_m A_M: R),
                F_totally_bounded_general A ->
                (0 < F + 1 <= #|D|)%N ->
                is_lim_seq (fun t:nat => m_general mal init A t) A_m ->
                is_lim_seq (fun t:nat => M_general mal init A t) A_M ->
                A_m <> A_M ->
                (A_m < A_M)%Re).
   { apply A_m_lt_A_M. } destruct H3. 
   specialize (H12 A_m A_M H3 H0 H5 H4 H10).
   apply const_ineq_exists in H12.


   (** use the definition of (F+1, F+1) robustness **)
   destruct H2 as [non_tri H2].
   rewrite /nonempty_nontrivial_graph in non_tri.
   specialize (H2 H0).
   (* Specialize S1 with X_M and S2 with X_m *)
   remember #|Normal_general A| as N.

   (* how do I introduce a time parameter here *)
   destruct H12 as [eps_0 H12].
   rewrite /wts_well_behaved_general in H1.
   (* rewrite /wts_well_behaved_at_t in H0. *)

   (** Desired contradiction ? **)
   (** The contradiction comes from the fact that 
      after some time t_eps + T, all normal nodes will have 
      value less than A_M -eps or < A_M
   **)
   assert (exists t:nat,  (M_general mal init A t < A_M)%Re \/ (m_general mal init A t > A_m)%Re).
   { assert (exists T:nat, (T<=N)%N).
     { exists (N)%N. by []. }
    
     destruct H1 as [a H1]. destruct H1 as [a_0 H1]. destruct H1 as [a_1 H1].
     assert (exists eps: posreal, (eps < a ^ N / (1 - a ^ N) * eps_0)%Re).
     { assert ((0 < a^N * eps_0)%Re).
       { apply Rmult_lt_0_compat.
         + apply a_j_pow_gt_0.
           - apply a_0.
           - rewrite HeqN. rewrite cardE.  by apply size_normal_gt_0.
           - apply posreal_cond.
       } exists (mkposreal (a^N * eps_0)%Re H15).
       simpl.
       assert ((a ^ N * eps_0)%Re = ((a ^ N * eps_0 * (1 - a^N)) * (/(1-a^N)))%Re).
       { assert ((a ^ N * eps_0 * (1 - a ^ N) * / (1 - a ^ N))%Re = 
                  ((a ^ N * eps_0)%Re * ((1 - a ^ N) * / (1 - a ^ N)))%Re).
         { nra. } rewrite H16.
         rewrite Rinv_r.
         + nra. 
         + assert ((0<  (1 - a ^ N))%Re -> (1 - a ^ N)%Re <> 0%Re).
           { nra. } apply H17.
           assert ((a^N <1)%Re -> (0 < 1 - a ^ N)%Re). { nra. } apply H18.
           apply a_j_pow_lt_l.
           - by [].
           - by [].
           - rewrite HeqN. rewrite cardE. destruct H. by apply size_normal_gt_0.
        } rewrite H16. clear H16.
        assert ((a ^ N / (1 - a ^ N) * eps_0)%Re = ((a^N * eps_0) * (/(1-a^N)))%Re).
        { nra. } rewrite H16. clear H16.
        apply Rmult_lt_compat_r.
        + apply Rinv_0_lt_compat.
          assert ((a^N <1)%Re -> (0 < 1 - a ^ N)%Re). { nra. } apply H16.
           apply a_j_pow_lt_l.
           - by [].
           - by [].
           - rewrite HeqN. rewrite cardE.  by apply size_normal_gt_0.
        + assert ((a ^ N * eps_0 * (1 - a ^ N))%Re = 
                   ( a ^ N * eps_0 - (a ^ N)^2 * eps_0)%Re).
          { nra. } rewrite H16.
          assert ((- ((a ^ N) ^ 2 * eps_0) < 0)%Re ->
                  (a ^ N * eps_0 - (a ^ N) ^ 2 * eps_0 < a ^ N * eps_0)%Re).
          { nra. } apply H17. clear H16 H17.
          apply Ropp_lt_gt_0_contravar.
          assert ( ((a ^ N) ^ 2 * eps_0)%Re = (a^N * (a ^ N * eps_0))%Re).
          { nra. } rewrite H16. clear H16.
          apply Rmult_lt_0_compat.
          - apply a_j_pow_gt_0.
            * by [].
            * rewrite HeqN. rewrite cardE. destruct H. by apply size_normal_gt_0.
            * by [].
      }

     destruct H15 as [eps H15].
     specialize (H8 eps). destruct H8 as [t_eps H8].


     assert ( X_M_t_e_i eps_0 A_M t_eps mal init A \proper Vertex /\
               (0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N ->
               X_m_t_e_i eps_0 A_m t_eps mal init A \proper Vertex /\
               (0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N ->
               [disjoint
                  X_M_t_e_i eps_0 A_M t_eps mal init A
                & X_m_t_e_i eps_0 A_m t_eps mal init A] ->
               (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
                    (F + 1)| ==
                #|X_M_t_e_i eps_0 A_M t_eps mal init A|)
               || ((#|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
                       (F + 1)| ==
                   #|X_m_t_e_i eps_0 A_m t_eps mal init A|)
               || (F + 1 <=
                   #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
                       (F + 1)| +
                   #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
                       (F + 1)|)%N )).
     (** Start with (t_eps, eps_0) **)
     { specialize (H2 (X_M_t_e_i eps_0 A_M t_eps mal init A) (X_m_t_e_i eps_0 A_m t_eps mal init A)).
       assert([|| #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)| ==
       #|X_M_t_e_i eps_0 A_M t_eps mal init A|,
       #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)| ==
       #|X_m_t_e_i eps_0 A_m t_eps mal init A|
       | (F + 1 <=
       #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)| +
       #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)|)%N] =
       (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)| ==
       #|X_M_t_e_i eps_0 A_M t_eps mal init A|)
       || (#|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)| ==
       #|X_m_t_e_i eps_0 A_m t_eps mal init A|) || (F + 1 <=
       #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)| +
       #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A) (F + 1)|)%N).
       {by destruct (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A) (F + 1)| ==
       #|X_M_t_e_i eps_0 A_M t_eps mal init A|).
       }
       rewrite H16. apply H2.
     }

     assert ( ( X_M_t_e_i eps_0 A_M t_eps mal init A \proper Vertex /\
               (0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N ->
               X_m_t_e_i eps_0 A_m t_eps  mal init A \proper Vertex /\
               (0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N ->
               [disjoint
                  X_M_t_e_i eps_0 A_M t_eps mal init A
                & X_m_t_e_i eps_0 A_m t_eps mal init A] ->
               (#|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
                    (F + 1)| ==
                #|X_M_t_e_i eps_0 A_M t_eps mal init A|)
               || ((#|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A )
                       (F + 1)| ==
                   #|X_m_t_e_i eps_0 A_m t_eps mal init A |)
               || (F + 1 <=
                   #|Xi_S_r (X_M_t_e_i eps_0 A_M t_eps mal init A)
                       (F + 1)| +
                   #|Xi_S_r (X_m_t_e_i eps_0 A_m t_eps mal init A)
                       (F + 1)|)%N ))->
             (forall j:nat, (0<j)%N -> (j<=N)%N ->
                (eps_j j eps_0 eps a < eps_j (j-1)%N eps_0 eps a)%Re ->   
                 ( ( (0 < #|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N mal init A) :&: Normal_general A|)%N ->
                      (#|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N mal init A) :&: Normal_general A| <
                  #| (X_M_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_M (t_eps+(j-1))%N mal init A) :&: Normal_general A|)%N) \/
                  ( (0 < #|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N mal init A) :&: Normal_general A|)%N ->
                    (#|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N mal init A) :&: Normal_general A| <
                      #| (X_m_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_m (t_eps+(j-1))%N mal init A) :&: Normal_general A|)%N)))).
    { rewrite HeqN. apply r_s_robustness_implies.
      + by [].
      + rewrite /wts_well_behaved_general. exists a. by split.
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + rewrite -HeqN. by [].
      + intros. specialize (H1 t i). (*specialize (H0 t i H17). *) destruct H1.
         destruct H17. by split.
    } specialize (H17 H16).
    

    assert ( (forall j:nat, (0<j)%N -> (j<=N)%N ->
                (eps_j j eps_0 eps a < eps_j (j-1)%N eps_0 eps a)%Re ->   
                 ( ( (0 < #|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N mal init A) :&: Normal_general A|)%N ->
                      (#|(X_M_t_e_i (eps_j j eps_0 eps a ) A_M (t_eps+j)%N mal init A) :&: Normal_general A| <
                  #| (X_M_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_M (t_eps+(j-1))%N mal init A) :&: Normal_general A|)%N) \/
                  ( (0 < #|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N mal init A) :&: Normal_general A|)%N ->
                    (#|(X_m_t_e_i (eps_j j eps_0 eps a ) A_m (t_eps+j)%N mal init A) :&: Normal_general A| <
                      #| (X_m_t_e_i (eps_j (j-1)%N eps_0 eps a)%N A_m (t_eps+(j-1))%N mal init A) :&: Normal_general A|)%N))) ->
              (exists t : nat, (M_general mal init A t < A_M)%Re \/ (m_general mal init A t > A_m)%Re)).
    { rewrite HeqN. apply normal_bound_exists.
      + by [].
      + rewrite /wts_well_behaved_general. exists a. by split.
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + by [].
      + rewrite -HeqN. by [].
      + intros. specialize (H1 t i). (*specialize (H0 t i H18) *) destruct H1.
        destruct H18. by split.
      + apply r_s_robustness_cond_implies.
        - by [].
        - by [].
        - rewrite /wts_well_behaved_general. by exists a.
        - by [].
        - by [].
        - by [].
        - by [].
        - apply H16.
          * assert ((0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N). 
            { apply X_M_card_gt_0.
              + by [].
              + by [].
              + rewrite /wts_well_behaved_general. by exists a.
              + by [].
              + by [].
            }
            assert ((0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N). 
            { apply X_m_card_gt_0.
              + by [].
              + by [].
              + rewrite /wts_well_behaved_general. by exists a.
              + by [].
              + by [].
            }
            assert (X_M_t_e_i eps_0 A_M t_eps mal init A \proper Vertex).
            { apply (@X_M_mem mal init A t_eps A_M A_m eps_0).
              + by apply ltn_trans with 1%N.
              + by [].
              + apply H19.
            } by split.
          * assert ((0 < #|X_M_t_e_i eps_0 A_M t_eps mal init A|)%N). 
            { apply X_M_card_gt_0.
              + by [].
              + by [].
              + rewrite /wts_well_behaved_general. by exists a.
              + by [].
              + by [].
            }
            assert ((0 < #|X_m_t_e_i eps_0 A_m t_eps mal init A|)%N). 
            { apply X_m_card_gt_0.
              + by [].
              + by [].
              + rewrite /wts_well_behaved_general. by exists a.
              + by [].
              + by [].
            }
            assert (X_m_t_e_i eps_0 A_m t_eps mal init A \proper Vertex).
            { apply (@X_m_mem mal init A t_eps A_M A_m eps_0).
              + by apply ltn_trans with 1%N.
              + by [].
              + apply H18.
            } by split.
          * by apply X_M_X_m_disjoint.
    } by specialize (H18 H17).
   }
   destruct H14 as [t H14].
   assert (forall t : nat, (m_general mal init A t <= A_m)%Re). 
   { by apply m_A_m_lower_bound. }
   specialize (H11 t). specialize (H15 t).
   assert ((M_general mal init A t >= A_M)%Re /\ (m_general mal init A t <= A_m)%Re ).
   { split.
     + by apply Rle_ge.
     + by [].
   }
   assert (~((M_general mal init A t < A_M)%Re \/ (m_general mal init A t > A_m)%Re)).
   { nra. } contradiction.
+ (** apply lemma 1 or a corollary of lemma 1 here **)
  by apply interval_bound.
Qed.


