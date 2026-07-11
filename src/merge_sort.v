(* begin hide *)
Require Import List.
Import ListNotations.
Require Import Recdef.
Require Import Arith.
Require Import Lia.
Require Import Sorted.
Require Import Permutation.
(* end hide *)

(** Neste trabalho formalizaremos a correção do algoritmo [mergesort]. Esta formalização envolve diversas etapas que incluem a definição de diferentes funções.  *)

(** O algoritmo [merge] a seguir recebe um par de listas ordenadas como argumento. A função [len] abaixo, define o tamanho de um par de listas: *)

Definition len (p:list nat * list nat) := length (fst p) + length (snd p).

Function merge (p: list nat * list nat) {measure len p}:=
  match p with
  | ([], l2) => l2
  | (l1, []) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
          if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
          else hd2 :: merge (l1, tl2)
  end.
Proof.
  - auto.
  - intros. unfold len. simpl. lia.
Qed.

Inductive ord: list nat -> Prop :=  
  | ord_nil: ord nil
  | ord_one: forall h, ord (h::nil)
  | ord_all: forall x y l, x <= y -> ord (y::l) -> ord (x::y::l).
  
Definition le_all x l := forall y, In y l -> x <= y.
Definition sorted_pair_lst (p: list nat * list nat) := ord (fst p) /\ ord (snd p).
     

Definition first_is_smallest (l : list nat) : Prop :=
  match l with
  | nil => True
  | hd :: tl => forall x, In x tl -> hd <= x
  end.


(** O algoritmo [mergesort] é definido como a seguir: *)

Function mergesort (l: list nat) {measure length l} :=
  match l with
  | [] => []
  | [h] => [h]
  | h1::h2::l' =>
      let l1_half := length(l)/2 in
      let l1 := firstn l1_half l in
      let l2 := skipn l1_half l in
      merge(mergesort l1 , mergesort l2)
  end.
  Proof.
  - intros. rewrite skipn_length. apply Nat.sub_lt.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
      * simpl. apply Nat.lt_0_succ.
        * apply Nat.lt_1_2.
      + apply Nat.div_str_pos. simpl. split.
      * apply Nat.lt_0_2.
        * apply Peano.le_n_S. apply Peano.le_n_S. apply Peano.le_0_n.  
    - intros. rewrite firstn_length. rewrite min_l.
    + apply Nat.div_lt.
      * simpl. apply Nat.lt_0_succ.
        * apply Nat.lt_1_2.
      + apply Nat.lt_le_incl. apply Nat.div_lt.
      * simpl. apply Nat.lt_0_succ.
        * apply Nat.lt_1_2.  
  Defined.


Theorem mergesort_correto: forall l, ord (mergesort l) /\
                                       Permutation (mergesort l) l.
Proof. Admitted.

