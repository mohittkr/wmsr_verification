Require Import Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra finset seq.
From GraphTheory Require Import digraph.
From Coquelicot Require Import Lim_seq Rbar.
From mathcomp.analysis Require Import Rstruct.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation diGraph := relType.
Notation di_edge := edge_rel.

(**** Define graph topology ******)

Variables (D: diGraph).

(** Define an F-paramter **)
Variable F:nat.


(** Define the vertex set **)
Definition Vertex : {set D}:= setT.

Parameter corrupt: D -> bool.

(** Define the set of adversary nodes **)
Definition Adversary := 
  [set x :D | (corrupt x == true)].

(** Define the set of normal nodes **)
Definition Normal:= Vertex :\: Adversary.


(** Show that the above definition of normal is equivalent
  to [set x :D | (corrupt x == false)] **)
Lemma set_not: forall (x:D) (P : pred D),
  (x \in ~: finset (fun x: D => P x)) && ( x \in [set : D]) =
  (x \in (finset (fun x : D => ~~ (P x)))).
Proof.
intros. rewrite /setT -in_setI !in_set. apply /andP.
case: (~~ P x).
+ auto.
+ apply /andP. auto.
Qed.


Lemma normal_equiv:
  Normal = [set x :D | (corrupt x == false)].
Proof.
rewrite /Normal /setD. apply eq_finset. unfold eqfun.
intros. rewrite -in_setC /= /Adversary /Vertex /=.
rewrite set_not in_set.
case: corrupt; auto.
Qed.


(** Define a set of in-neighbors :
  set of neighbors of i such that for any 
  j in the set, j--i is a valid edge relation in the 
  graph
**)
Definition in_neighbor (i:D) := [set j : D | j -- i].


(** Define the in-degree of i **)
Definition in_degree (i:D):= #|in_neighbor i|.

(** Define a set of out-neighbors:
  set of neigbors of i such that information 
  flows from i to j 
**)
Definition out_neighbor (i:D) := [set j:D | i -- j].

(** Define a set of inclusive neighbors:
  union of the set of in-neighbors and i itself **)
Definition inclusive_neigh (i:D) := 
   (in_neighbor i) :|: set1 i.


(** Define a r-reachable set **)
Definition r_reachable (r:nat) (S: {set D}):=
  S \proper Vertex /\ (#|S| > 0)%N /\
  (forall i:D, i \in S -> (#| (in_neighbor i) :\: S| >= r)%N).


(** Define a non-empty and non-trivial digraph **)
Definition nonempty_nontrivial_graph:= (#|D| >= 2)%N.

(** Define r-robustness **)
Definition r_robustness (r: nat):=
  nonempty_nontrivial_graph /\ 
  (forall (S1 S2: {set D}), 
      (S1 \proper Vertex /\ (#|S1|>0)%N) ->
      (S2 \proper Vertex /\ (#|S2|>0)%N) ->
      [disjoint S1 & S2] ->
      (r_reachable r S1 \/ r_reachable r S2)).
 
(** Define (r,s)-reachable set **)

(* Define Xi_S_r **)
Definition Xi_S_r (S: {set D}) (r:nat):= 
  [set i:D | i \in S & (#| (in_neighbor i) :\: S| >= r)%N].

Definition r_s_reachable (S: {set D}) (r s:nat):=
  (S \proper Vertex /\ (#|S| > 0)%N) -> (#|Xi_S_r S r| >= s)%N.

(** Define (r,s)-robustness **)
Definition r_s_robustness (r s:nat):=
  nonempty_nontrivial_graph /\
  ( (1 <= s <= #|D|)%N ->
    forall (S1 S2: {set D}), 
      (S1 \proper Vertex /\ (#|S1|>0)%N) ->
      (S2 \proper Vertex /\ (#|S2|>0)%N) ->
      [disjoint S1 & S2] -> 
      ( (#|Xi_S_r S1 r| == #|S1|) || 
        ((#|Xi_S_r S2 r| == #|S2|) ||
        (#|Xi_S_r S1 r| + #|Xi_S_r S2 r| >=s))%N )).


(*** Define the threat model and the W_MSR update ***)

(** **)
Parameter x_mal : nat -> D -> R.
 
(** Define w as a parameter associating 
 an edge e in D with a real value at time t **)
Parameter w : nat -> D*D -> R.


(** define list of verticies **)
Definition inclusive_neighbor_list (i:D) := enum (inclusive_neigh i).


Definition remove_extremes (i:D) (l:seq D) (x:nat -> D -> R) (t:nat) : (seq D) :=
  filter (fun (j:D) => (((Rge_dec (x t j) (x t i)) || (F <= (index j l))%N) &&
  ( Rle_dec (x t j) (x t i)  || (index j l <= ((size l) - F - 1))%N))) l.

(** gets inclusive neighbors of i and removes values **)
Definition incl_neigh_minus_extremes (i:D) (x:nat -> D -> R) (t:nat) : (seq D) :=
  remove_extremes i (inclusive_neighbor_list i) x t.


(** values of nodes at time 0 **)
Parameter x0 : D -> R.

Fixpoint x (t:nat) (i:D) :=
  match (corrupt i) with
  |true => x_mal t i
  |false =>
  (match t with
    | O => x0 i
    | S t' => sum_f_R0 (fun n:nat => let j := (nth i (incl_neigh_minus_extremes i x t') n) in
       ((x t' j) * (w t' (i,j)))%Re) ((size (incl_neigh_minus_extremes i x t'))-1)
   end)
  end.
(**
Fixpoint x_norm (t:nat) (i:D) :=
  match t with
    | O => x0 i
    | S t' => sum_f_R0 (fun n:nat => let j := (nth i (incl_neigh_minus_extremes i x t') n) in
       ((x t' j) * (w t' (i,j)))%Re) ((size (incl_neigh_minus_extremes i x t'))-1)
   end.


(** inductively constructs x at time t given initial value **)
Definition x (t:nat) (i:D) :=
  match (corrupt i) with
  |true => x_mal t i
  |false => x_norm t i
  end.
**)

Definition R_i_greater_than_maybe_not_neighbors (i:D) (t:nat) :=
  [set j | Rgt_dec (x t j) (x t i) &&
  (index j (inclusive_neighbor_list i) >
  ((size (inclusive_neighbor_list i)) - F - 1))%N].

Definition R_i_greater_than (i:D) (t:nat) :=
  [set j | Rgt_dec (x t j) (x t i) &&
  (index j (inclusive_neighbor_list i) >
  ((size (inclusive_neighbor_list i)) - F - 1))%N &&
  (j \in (inclusive_neighbor_list i))].

Definition R_i_less_than_maybe_not_neighbors (i:D) (t:nat) :=
  [set j | (Rlt_dec (x t j) (x t i)) &&
  (index j (inclusive_neighbor_list i) < F)%N].

Definition R_i_less_than (i:D) (t:nat) :=
  [set j | (Rlt_dec (x t j) (x t i)) &&
  (index j (inclusive_neighbor_list i) < F)%N &&
  (j \in (inclusive_neighbor_list i))].

(** defines maliciousness for vertex i at time t **)
Definition malicious_at_i_t (i:D) (t:nat) : bool := 
(x (t+1) i) != sum_f_R0 (fun n:nat => let j := (nth i (incl_neigh_minus_extremes i x t) n) in
       ((x t j) * (w t (i,j)))%Re) ((size (incl_neigh_minus_extremes i x t))-1).


(** Define maliciousness **)
Definition malicious (i:D) := 
exists t:nat,  malicious_at_i_t i t.

(** defines condition for weights given in W-MSR at time t **)
Definition wts_well_behaved:= 
  exists a:R, (0<a)%Re /\ (a <1)%Re /\
  (forall (t:nat) (i:D), 
    (*i \in Normal ->  *)
    (forall j:D, j \notin ((incl_neigh_minus_extremes i x t)) -> (w t (i,j) = 0)%Re) /\
      (forall j:D, j \in ((incl_neigh_minus_extremes i x t)) ->(a <= w t (i,j)))%Re /\
      sum_f_R0 (fun n:nat => let j := (nth i (incl_neigh_minus_extremes i x t) n) in
       (w t (i,j))%Re) ((size (incl_neigh_minus_extremes i x t))-1) = 1%Re).



(*
Definition wts_well_behaved_at_t (t:nat) :=
  forall i:D, i \in Normal -> ((forall j:D, j \notin ((incl_neigh_minus_extremes i x t)) -> (w t (i,j) = 0)%Re) /\
  (exists a:R, (a > 0)%Re /\ (forall j:D, j \in ((incl_neigh_minus_extremes i x t)) ->(a < w t (i,j)))%Re) /\
  (sum_f_R0 (fun n:nat => let j := (nth i (incl_neigh_minus_extremes i x t) n) in
       (w t (i,j))%Re) ((size (incl_neigh_minus_extremes i x t))-1)) = 1
  ).

(** defines condition for weights given in W-MSR **)
Definition wts_well_behaved := forall t:nat, wts_well_behaved_at_t t.

*)
(** Define an F_total set S **)
Definition F_total (S: {set D}) :=
  S \proper Vertex /\ (#|S| <= F)%N.

(** Define a F-totally bounded set of adversary nodes **)
Definition F_totally_bounded := F_total Adversary.

(** Define an F-total malicious network **)
Definition F_total_malicious := F_totally_bounded /\
  (forall i:D, i \in Adversary -> malicious i) /\
  (forall j:D, j \in Normal -> ~ (malicious j)).

(** defines min and max values of normal nodes **)
Definition m (t:nat) : R :=
  -(bigmaxr 0 ((map (fun i:D => -(x t i))) (enum Normal))).
Definition M (t:nat) : R :=
  bigmaxr 0 (map (x t) (enum Normal)).

(** defines resilient asymptotic consensus **)
Definition Resilient_asymptotic_consensus:=
  F_total_malicious -> 
     ( (exists L:Rbar,
          forall (i:D), i \in Normal ->
          is_lim_seq (fun t: nat => x t i) L) /\ 
      (forall t:nat,  (m 0 <= m t)%Re /\ (M t <= M 0)%Re)).

