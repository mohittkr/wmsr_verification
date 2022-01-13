Require Import Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra finset seq.
From GraphTheory Require Import digraph.
From Coquelicot Require Import Lim_seq Rbar.
From mathcomp.analysis Require Import Rstruct.
From Coq Require Import Logic.FunctionalExtensionality.

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


(** Define the set of advversary nodes **)
Definition Adversary_general (corrupt_choice:D -> bool):=
  [set x:D | corrupt_choice x == true].

(** Defines set of normal nodes **)
Definition Normal_general (corrupt_choice:D -> bool):=
  Vertex :\: Adversary_general corrupt_choice.


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

(** Define (r,s)-reachability  **)
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
        (#|Xi_S_r S2 r| == #|S2|) ||
        (#|Xi_S_r S1 r| + #|Xi_S_r S2 r| >=s)%N )).


(*** Define the threat model and the W_MSR update ***)
 
(** Define w as a parameter associating 
 an edge (i, j) in D with a real value at time t **)
Parameter w : nat -> D*D -> R.


(** define list of verticies **)
Definition inclusive_neighbor_list (i:D) := enum (inclusive_neigh i).

(** removes nodes in top F of list and greater than x t i or
in bottom F of list and less than x t i **)
Definition remove_extremes (i:D) (l:seq D) (x:nat -> D -> R) (t:nat) : (seq D) :=
  filter (fun (j:D) => (((Rge_dec (x t j) (x t i)) || (F <= (index j l))%N) &&
  ( Rle_dec (x t j) (x t i)  || (index j l <= ((size l) - F - 1))%N))) l.

(** gets inclusive neighbors of i and removes values **)
Definition incl_neigh_minus_extremes (i:D) (x:nat -> D -> R) (t:nat) : (seq D) :=
  remove_extremes i (inclusive_neighbor_list i) x t.

(** define the value of a node at time **)
Fixpoint x_general (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat) (i:D) :=
  match (A i) with
  |true => mal t i
  |false =>
  (match t with
    | O => init i
    | S t' => sum_f_R0 (fun n:nat => let j :=
       (nth i (incl_neigh_minus_extremes i (x_general mal init A) t') n) in
       (((x_general mal init A) t' j) * (w t' (i,j)))%Re) ((size (incl_neigh_minus_extremes i (x_general mal init A) t'))-1)
   end)
  end.


(** Defines the set of nodes, greater than
 x_general mal init A t i, with values
in the top F of the inclusive_neighbor_list **)
Definition R_i_greater_than_general
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (i:D) (t:nat) :=
[set j | Rgt_dec ((x_general mal init A) t j)
((x_general mal init A) t i) &&
(index j (inclusive_neighbor_list i) >
((size (inclusive_neighbor_list i)) - F - 1))%N &&
(j \in (inclusive_neighbor_list i))].

(** Defines the set of nodes, greater than
 x_general mal init A t i, with values
in the top F of the inclusive_neighbor_list, or potentially not in 
inclusive_neighbor_list **)
Definition R_i_greater_than_maybe_not_neighbors_general
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (i:D) (t:nat) :=
[set j | Rgt_dec ((x_general mal init A) t j)
((x_general mal init A) t i) &&
(index j (inclusive_neighbor_list i) >
((size (inclusive_neighbor_list i)) - F - 1))%N].

(** Defines the set of nodes, less than
 x_general mal init A t i, with values
in the top bottom of the inclusive_neighbor_list, or potentially not in 
inclusive_neighbor_list **)
Definition R_i_less_than_maybe_not_neighbors_general
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (i:D) (t:nat) :=
[set j | (Rlt_dec ((x_general mal init A) t j)
((x_general mal init A) t i)) &&
(index j (inclusive_neighbor_list i) < F)%N].

(** Defines the set of nodes, less than
 x_general mal init A t i, with values
in the bottom F of the inclusive_neighbor_list **)
Definition R_i_less_than_general
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (i:D) (t:nat) :=
[set j | (Rlt_dec ((x_general mal init A) t j)
((x_general mal init A) t i)) &&
(index j (inclusive_neighbor_list i) < F)%N &&
(j \in (inclusive_neighbor_list i))].

(** Defines condition for a node to have malicious behavior at a 
given time **)
Definition malicious_at_i_t_general
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (i:D) (t:nat): bool :=
(x_general mal init A (t+1) i) != sum_f_R0 (fun n:nat =>
let j := (nth i (incl_neigh_minus_extremes i (x_general mal init A) t) n) in
((x_general mal init A t j) * (w t (i,j)))%Re) ((size (incl_neigh_minus_extremes i (x_general mal init A) t))-1).

(** Define maliciousness **)
Definition malicious_general
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (i:D) := 
exists t:nat, malicious_at_i_t_general mal init A i t.

(** defines condition for weights given in W-MSR at time t **)
Definition wts_well_behaved_general (A:D -> bool) (mal:nat -> D -> R) (init:D -> R) := 
exists a:R, (0<a)%Re /\ (a <1)%Re /\
(forall (t:nat) (i:D),
(forall j:D, j \notin ((incl_neigh_minus_extremes i (x_general mal init A) t)) -> (w t (i,j) = 0)%Re) /\
(forall j:D, j \in ((incl_neigh_minus_extremes i (x_general mal init A) t)) ->(a <= w t (i,j)))%Re /\
sum_f_R0 (fun n:nat => let j := (nth i (incl_neigh_minus_extremes i (x_general mal init A) t) n) in
(w t (i,j))%Re) ((size (incl_neigh_minus_extremes i (x_general mal init A) t))-1) = 1%Re).

(** Define an F_total set S **)
Definition F_total (S: {set D}) :=
  S \proper Vertex /\ (#|S| <= F)%N.

(** Define a F-totally bounded set of adversary nodes **)
Definition F_totally_bounded_general (A:D -> bool) :=
F_total (Adversary_general A).

(** Define an F-total malicious network **)
Definition F_total_malicious_general
(mal:nat -> D -> R) (init:D -> R) (A:D -> bool) :=
F_totally_bounded_general A /\
(forall i:D, i \in Adversary_general A -> malicious_general mal init A i) /\
(forall j:D, j \in Normal_general A -> ~ (malicious_general mal init A j)).

(** defines min and max values of normal nodes **)
Definition m_general (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat): R :=
  -(bigmaxr 0 ((map (fun i:D => -(x_general mal init A t i)))
  (enum (Normal_general A)))).
Definition M_general (mal:nat -> D -> R) (init:D -> R) (A:D -> bool) (t:nat): R :=
  bigmaxr 0 (map (x_general mal init A t) (enum (Normal_general A))).

(** defines resilient asymptotic consensus **)
Definition Resilient_asymptotic_consensus_general (A:D -> bool) (mal:nat -> D -> R) (init:D -> R):=
(F_total_malicious_general mal init A) -> (exists L:Rbar,
forall (i:D), i \in (Normal_general A) ->
is_lim_seq (fun t: nat => x_general mal init A t i) L) /\ 
(forall t:nat,  (m_general mal init A 0 <= m_general mal init A t)%Re /\
(M_general mal init A t <= M_general mal init A 0)%Re).
