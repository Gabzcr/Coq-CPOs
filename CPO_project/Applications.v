From Coq Require Import Arith.
Require Import Psatz.
Require Export Setoid Morphisms.
Set Implicit Arguments.

From Project Require Import FiniteSet.
From Project Require Import CPO.

Require Import Bool.
Require Import Coq.Lists.List.

Section TruthValueInstances.

Program Instance Prop_B : B_param :=
  {|
    B := Prop;
    K A := True;
    is_true P := P;
    BTrue := True;
    BFalse := False;
    BAnd := and;
    BOr := or;
    BImpl P Q := P -> Q;
    BForall V Pv := forall v, Pv v;
    BExists V Pv := exists v, Pv v;
    memo X P := P
  |}.


Program Definition bool_fin : fin bool := {| el := cons true (cons false nil) |}.
Next Obligation. destruct a; destruct b. now left. now right. now right. now left. Qed.
Next Obligation. destruct a. now left. right. now left. Qed.

 Fixpoint is_member {X} {Xfin : fin X} (x:X) l := match l with 
  | nil => false
  | h :: q => (eq_bool Xfin x h) || (@is_member X Xfin x q)
  end.

 Lemma is_member_invariant {X} {Xfin : fin X} P : 
  forall x l, Is_true (is_member (Xfin := Xfin) x (filter P l)) -> List.In x l.
 Proof.
  induction l.
  + now cbn.
  + cbn. destruct (P a) eqn:Pa. cbn. intro H. apply orb_prop_elim in H. destruct H.
    left. unfold eq_bool in H. destruct (eq_dec Xfin x a). now symmetry. contradict H.
    right. now apply IHl.
    intro H. right. now apply IHl.
 Qed.

 Program Instance Bool_B : B_param :=
  {|
    B := bool;
    K := fin;
    is_true := Is_true;
    BTrue := true;
    BFalse := false;
    BAnd := andb;
    BOr := orb;
    BImpl := implb;
    BForall V := fun P => List.forallb P (el (projT2 V));
    BExists V := fun P => List.existsb P (el (projT2 V));
    memo X P := let l := List.filter P (el (projT2 X)) in
                        fun x => is_member x l;
  |}.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. exists (el (@funP A X P)). apply (eq_dec (@funP A X P)).
   apply (all_el (@funP A X P)). Defined.
  Next Obligation. exists (el (@funAB A B X X0)). apply (eq_dec (@funAB A B X X0)).
   apply (all_el (@funAB A B X X0)). Defined.
  Next Obligation. exists (el (@funAbool A X)). apply (eq_dec (@funAbool A X)).
   apply (all_el (@funAbool A X)). Defined.
  Next Obligation.
    split; intro Q. apply Is_true_eq_left. apply List.forallb_forall. 
    intros x Hx. apply Is_true_eq_true. apply Q.
    intro x. apply Is_true_eq_left. apply Is_true_eq_true in Q. rewrite List.forallb_forall in Q.
    apply Q. cbn in *. apply (all_el X).
  Qed.
  Next Obligation.
    split; intro Q. destruct Q as [x Hx]. apply Is_true_eq_left. apply List.existsb_exists.
    exists x. split. cbn in *. apply (all_el X). now apply Is_true_eq_true.
    apply Is_true_eq_true in Q. apply List.existsb_exists in Q. destruct Q as [x Hx]. exists x.
    apply Is_true_eq_left. apply Hx. Qed.
  Next Obligation.
    cbn in *.
    assert (forall l x, List.In x l -> Is_true (is_member (Xfin := X0) x (filter P l)) <-> Is_true (P x)).
    + induction l.
      - intros y H. cbn; intuition.
      - intros y H. cbn. destruct (eq_dec X0 y a).
        * rewrite <- e. cbn. destruct (P y) eqn : Py; cbn; intuition.
        apply orb_prop_intro. left. unfold eq_bool. destruct (eq_dec X0 y y). now cbn. now contradict n.
        apply IHl in H0. rewrite Py in H0. contradict H0. now apply (is_member_invariant (Xfin := X0)) with P.
        * inversion H. symmetry in H0. now contradict H0.
          destruct (P a) eqn:HPa. cbn. destruct (P y) eqn:HPy; cbn. split; try auto. intro. apply orb_prop_intro.
          right. apply IHl. assumption. now rewrite HPy.
          split; try auto. intro. apply orb_prop_elim in H1. destruct H1. unfold eq_bool in H1.
          destruct (eq_dec X0 y a). now contradict e. now contradict H1.
          apply IHl in H1. apply Is_true_eq_true in H1. contradict HPy. now rewrite H1. assumption.
          intuition. now apply IHl.
   + apply H. apply all_el.
   Qed.

End TruthValueInstances.


Program Definition eqbool {X : Type} {X_fin : fin X} (x y : X) : bool := match (eq_dec X_fin x y) with
  | left _ => true
  | right _ => false
  end.

Lemma eqbool_refl {X : Type} {X_fin : fin X} : 
  forall (x y : X), x = y <-> Is_true (eqbool (X_fin := X_fin) x y).
  Proof. intros. unfold eqbool. now destruct (eq_dec X_fin x y). Qed.

Lemma eqbool_trans {X : Type} {X_fin : fin X} : 
  forall (x y z : X), Is_true (eqbool (X_fin := X_fin) x y) -> 
                      Is_true (eqbool (X_fin := X_fin) y z) -> 
                      Is_true (eqbool (X_fin := X_fin) x z).
 Proof. intros x y z Hxy Hyz. unfold eqbool in *.
  destruct (eq_dec X_fin x y); destruct (eq_dec X_fin y z);
  destruct (eq_dec X_fin x z); try easy.
  contradict n. now rewrite e. Qed.




Section FiniteOrder.

 Context {X : valid_type} {P' : @B_PO Bool_B X}.
 Variable bottom : X.
 Hypothesis bottom_is_bot : forall (x : X), is_true (leq bottom x).
 
 Fixpoint update_candidates (element : X) (candidates : list X) : (list X) := match candidates with
  | nil => cons element nil
  | h :: q => if (leq h element) then update_candidates element q 
              else if (leq element h) then candidates
              else h :: (update_candidates element q)
  end.
  
 Fixpoint build_sup_candidate_aux (D : X -> bool) el_list candidates : (list X) := match el_list with
  | nil => candidates
  | h :: q => if (D h) then build_sup_candidate_aux D q (update_candidates h candidates)
            else build_sup_candidate_aux D q candidates
  end.
 
 Definition build_sup_candidate (D : X -> bool) :=
  build_sup_candidate_aux D (el (projT2 X)) nil.
 
 
 
 (* ----- Proof of properties on this program ----- *)
 (* We need to show that in the end the list of candidates we get contains either nothing 
    or 1 element that is the sup of D. *)
 
 (** * General useful properties *)

 Lemma update_adds_el_and_retrieve_others : forall el l x, In x (update_candidates el l) ->
  In x l \/ (x = el).
 Proof. induction l.
 + cbn. intros. destruct H. now right. now left.
 + intros. cbn in *. destruct (leq a el). destruct (IHl x). assumption.
  left. now right. now right. destruct (leq el a). inversion H. left. now left.
  left. now right. inversion H. left. now left. destruct (IHl x). assumption. left. now right.
  now right.
 Qed.
 
 
 (** * Elements in the list are not comparable *)
 
 Definition incomparable l := forall x y, In x l -> In y l -> (x = y) \/ (~ x <= y /\ ~ y <= x).
 
 Lemma included_stays_incomparable : forall l a, incomparable (a::l) -> incomparable l.
 Proof. unfold incomparable. intros. apply H; now apply in_cons. Qed.
 
 Lemma update_preserves_incomparable : forall el cand, 
  incomparable cand -> incomparable (update_candidates el cand).
 Proof.
  intros el cand Hincomp x y Hx Hy.
  induction cand. cbn in Hx, Hy. destruct Hx; destruct Hy; try (now intuition).
  left. rewrite <- H. now rewrite <- H0.
  cbn in Hx, Hy. destruct (leq a el) eqn:EQ.
  apply included_stays_incomparable in Hincomp. now apply IHcand.
  destruct (leq el a) eqn:EQ2. now apply Hincomp.
  inversion Hx; inversion Hy. left. rewrite <- H. now rewrite <- H0.
  
  destruct (update_adds_el_and_retrieve_others el cand y H0).
  apply Hincomp. rewrite H. apply in_eq. now apply in_cons.
  rewrite <- H. rewrite H1. right. split;
  unfold leq_in_prop; intro; apply Is_true_eq_true in H2; contradict H2.
  now rewrite EQ. now rewrite EQ2.
  
  destruct (update_adds_el_and_retrieve_others el cand x H).
  apply Hincomp. now apply in_cons. rewrite H0. apply in_eq.
  rewrite <- H0. rewrite H1. right. split;
  unfold leq_in_prop; intro; apply Is_true_eq_true in H2; contradict H2.
  now rewrite EQ2. now rewrite EQ.
  
  apply IHcand; try assumption. now apply included_stays_incomparable with a.
 Qed.

 Lemma aux_preserves_incomparable D lst cand : 
  incomparable cand -> incomparable (build_sup_candidate_aux D lst cand).
 Proof.
  revert cand. induction lst.
  + intros cand H. now cbn.
  + intros cand H. cbn. destruct (D a). apply IHlst. now apply update_preserves_incomparable.
    now apply IHlst.
 Qed.

 Lemma candidates_are_incomparable D : incomparable (build_sup_candidate D).
 Proof. unfold build_sup_candidate. now apply aux_preserves_incomparable. Qed.
 
 
  (** * Elements in the list are in D *)
 
 Lemma candidates_are_in_D_aux D cand lst : (forall x, In x cand -> Is_true (D x)) ->
  forall x, In x (build_sup_candidate_aux D lst cand) -> Is_true (D x).
 Proof.
  revert cand. induction lst. intro. unfold build_sup_candidate.
  + now cbn.
  + cbn. destruct (D a) eqn:EQDa. 
    - intros. apply IHlst with (update_candidates a cand).
      intros x0 Hx0. apply update_adds_el_and_retrieve_others in Hx0. destruct Hx0. now apply H.
      rewrite H1. now apply Is_true_eq_left. assumption.
     - apply IHlst.
  Qed.

Lemma candidates_are_in_D D : forall x, In x (build_sup_candidate D) -> Is_true (D x).
Proof.
  apply candidates_are_in_D_aux. now cbn.
 Qed.
 
 
 (** * Elements in the list have no duplicates *)

 Lemma update_preserves_NoDup : forall a cand, NoDup cand -> NoDup (update_candidates a cand).
 Proof.
  induction cand.
  + cbn. intro. now constructor.
  + intro. cbn. destruct (leq a0 a) eqn:EQa0a.
    - apply NoDup_cons_iff in H. destruct H. now apply IHcand.
    - destruct (leq a a0). assumption. apply NoDup_cons_iff in H. destruct H. constructor.
      intro. apply update_adds_el_and_retrieve_others in H1. destruct H1. now contradict H1.
      rewrite H1 in EQa0a. contradict EQa0a. assert (leq a a = true). apply Is_true_eq_true. reflexivity.
      now rewrite H2.
      now apply IHcand.
  Qed.


 Lemma aux_preserves_NoDUp D cand lst : 
  NoDup cand -> NoDup (build_sup_candidate_aux D lst cand).
 Proof.
  revert cand. induction lst. intro. unfold build_sup_candidate.
  + now cbn.
  + cbn. destruct (D a) eqn:EQDa. 
    - intros. apply IHlst. now apply update_preserves_NoDup.
     - apply IHlst.
  Qed.

 Lemma candidates_have_no_duplicate D : NoDup (build_sup_candidate D).
 Proof. apply aux_preserves_NoDUp. constructor. Qed.



  (** * Elements in the list dominate every elements in D (this will come progressively) *)

 Lemma update_contains_bigger : forall el cand, exists el0, In el0 (update_candidates el cand) /\ el <= el0.
 Proof.
 induction cand.
 + exists el. split. cbn. now left. reflexivity.
 + cbn. destruct (leq a el) eqn:EQ1. apply IHcand. destruct (leq el a) eqn:EQ2. exists a.
  split. apply in_eq. now apply Is_true_eq_left. cbn. destruct IHcand as [x [Hx1 Hx2]].
  exists x. split. now right. apply Hx2.
 Qed.

 Lemma update_preserves_domination : forall el cand x, 
  (exists y, In y cand /\ x <= y) -> (exists y, In y (update_candidates el cand) /\ x <= y).
 Proof.
  induction cand.
  + intros. destruct H as [y [Hy Hxy]]. contradict Hy.
  + intros x Hx. destruct Hx as [y [Hy Hxy]]. destruct Hy as [Hy | Hy].
    - cbn. destruct (leq a el) eqn:EQ.  
      * destruct (update_contains_bigger el cand) as [s Hs]. destruct Hs as [Hs Hels].
        exists s. split. assumption. assert (x <= s). rewrite <- Hels. rewrite Hxy. rewrite <- Hy. cbn.
        apply Is_true_eq_left. apply EQ. apply H.
      * destruct (leq el a). exists a. split. apply in_eq. rewrite Hy. apply Hxy. 
        exists a. split. apply in_eq. rewrite Hy. apply Hxy.
    - cbn in *. destruct (leq a el). apply IHcand. now exists y.
      destruct (leq el a). exists y. split. now apply in_cons. assumption.
      destruct (IHcand x) as [s [Hs1 Hs2]]. now exists y.
      exists s. split. now apply in_cons. assumption.
 Qed.


 Lemma In_update_is_commutative : forall l x y z, 
  (exists z', In z' (update_candidates x (update_candidates y l)) /\ z <= z') 
  <-> (exists z', In z' (update_candidates y (update_candidates x l)) /\ z <= z').
 Proof.
  induction l.
  + intros x y z. cbn. destruct (leq x y) eqn:EQxy; destruct (leq y x)eqn:EQyx.
    - split; intro. exists y. split. apply in_eq. destruct H as [z' [Hz'x Hzz']].
    inversion Hz'x. rewrite <- H in Hzz'. transitivity x. assumption. now apply Is_true_eq_left.
    contradict H.
    exists x. split. apply in_eq. destruct H as [z' [Hz'x Hzz']].
    inversion Hz'x. rewrite <- H in Hzz'. transitivity x. transitivity y. assumption. now apply Is_true_eq_left.
    reflexivity. contradict H.
    - reflexivity.
    - reflexivity.
    - split; intro. destruct H as [z' [Hz'1 Hz'2]]. inversion Hz'1. exists y. split. apply in_cons. apply in_eq.
    now rewrite <- H in Hz'2. inversion H. exists x. split. apply in_eq. now rewrite <- H0 in Hz'2.
    contradict H0.
    destruct H as [z' [Hz'1 Hz'2]]. inversion Hz'1. exists x. split. apply in_cons. apply in_eq.
    now rewrite <- H in Hz'2. inversion H. exists y. split. apply in_eq. now rewrite <- H0 in Hz'2.
    contradict H0.
  + intros. split; intro.
    - destruct H as [z' [Hz' Hzz']]. apply update_adds_el_and_retrieve_others in Hz'.
      destruct Hz' as [Hz' | Hz']. apply update_adds_el_and_retrieve_others in Hz'. destruct Hz'.
      repeat apply update_preserves_domination. now exists z'.
      destruct (update_contains_bigger y (update_candidates x (a :: l))) as [z'0 [Hz'0 Hyz'0]].
      exists z'0. split. assumption. rewrite <- Hyz'0. rewrite Hzz'. now rewrite H.
      apply update_preserves_domination.
      destruct (update_contains_bigger x (a :: l)) as [z'0 [Hz'0 Hyz'0]].
      exists z'0. split. assumption. rewrite <- Hyz'0. rewrite Hzz'. now rewrite Hz'.
    - destruct H as [z' [Hz' Hzz']]. apply update_adds_el_and_retrieve_others in Hz'.
      destruct Hz' as [Hz' | Hz']. apply update_adds_el_and_retrieve_others in Hz'. destruct Hz'.
      repeat apply update_preserves_domination. now exists z'.
      destruct (update_contains_bigger x (update_candidates y (a :: l))) as [z'0 [Hz'0 Hyz'0]].
      exists z'0. split. assumption. rewrite <- Hyz'0. rewrite Hzz'. now rewrite H.
      apply update_preserves_domination.
      destruct (update_contains_bigger y (a :: l)) as [z'0 [Hz'0 Hyz'0]].
      exists z'0. split. assumption. rewrite <- Hyz'0. rewrite Hzz'. now rewrite Hz'.
  Qed.


 Lemma build_sup_preserves_domination D : forall lst cand x, Is_true (D x) ->
  (exists y, In y cand /\ x <= y) ->
  exists y, In y (build_sup_candidate_aux D lst cand) /\ x <= y.
 Proof.
  induction lst.
  + intros cand x Dx Hx. cbn. apply Hx.
  + intros cand x Dx Hx. cbn in *. destruct (D a) eqn:EQ.
    - apply IHlst. assumption. pose proof update_preserves_domination. cbn in H. now apply H.
    - now apply IHlst.
 Qed.

 Lemma build_sup_preserves_eq_of_domination D lst x : forall cand1 cand2,
    ((exists y, In y cand1 /\ x <= y) <-> (exists y, In y cand2 /\ x <= y)) ->
    (exists y, In y (build_sup_candidate_aux D lst cand1) /\ x <= y) 
      <-> (exists y, In y (build_sup_candidate_aux D lst cand2) /\ x <= y).
  Proof.
    induction lst.
    + intros. cbn in *. apply H.
    + intros.
      cbn in *. destruct (D a).
      - apply IHlst. split; intros [z [Hz Hxz]].
        * pose proof update_adds_el_and_retrieve_others as InvUpdate.
          apply (InvUpdate a cand1 z) in Hz. destruct Hz.
          pose proof update_preserves_domination as Dom. cbn in Dom. apply Dom.
          apply H. now exists z. destruct update_contains_bigger with a cand2 as [a' [Ha' Haa']].
          exists a'. split. assumption. transitivity a. now rewrite <- H0. apply Haa'.
        * pose proof update_adds_el_and_retrieve_others as InvUpdate.
          apply (InvUpdate a cand2 z) in Hz. destruct Hz.
          pose proof update_preserves_domination as Dom. cbn in Dom. apply Dom.
          apply H. now exists z. destruct update_contains_bigger with a cand1 as [a' [Ha' Haa']].
          exists a'. split. assumption. transitivity a. now rewrite <- H0. apply Haa'.
      - now apply IHlst.
  Qed.

 Lemma build_sup_domination_update_elim D : forall lst cand x y,
  (exists z, In z (build_sup_candidate_aux D lst (update_candidates y cand)) /\ x <= z)
  -> exists z, (In z (build_sup_candidate_aux D lst cand) \/ z <= y) /\ x <= z.
  Proof.
    induction lst.
    + intros. cbn in *. induction cand. 
      - cbn in *. destruct H as [z Hz]. exists z. destruct Hz. destruct H. split. right. now rewrite H. assumption.
        contradict H.
      - cbn in *. destruct (leq a y) eqn:EQay.
        * destruct IHcand as [z Hz]. apply H.
          destruct Hz. destruct H0. exists z. split. left. now right. assumption.
          exists y. split. now right. now transitivity z.
        * destruct (leq y a); destruct H as [z [Hz Hxz]]; inversion Hz.
          exists z. split. left. now left. assumption.
          exists z. split. left. now right. assumption.
          exists z. split. left. now left. assumption.
          destruct IHcand as [s [Hs Hxs]]. now exists z. exists s. split.
          destruct Hs. left. now right. now right. assumption.
    + intros. cbn in *. destruct (D a) eqn:EQDa.
      * apply IHlst.
        pose proof build_sup_preserves_eq_of_domination as RW. 
        specialize RW with D lst x (update_candidates y (update_candidates a cand)) 
                                   (update_candidates a (update_candidates y cand)).
        apply RW. apply In_update_is_commutative. clear RW. apply H.
      * apply IHlst. apply H.
  Qed.

 Lemma build_sup_domination_preserves_inclusion D : forall lst cand x a, Is_true (D x) -> Is_true (D a) ->
  (exists y, In y (build_sup_candidate_aux D lst cand) /\ x <= y)
  -> exists y, In y (build_sup_candidate_aux D lst (a::cand)) /\ x <= y.
 Proof.
  induction lst.
  - intros. cbn in *. destruct H1 as [y Hy]. exists y. split. now right. apply Hy.
  - intros. cbn in *. destruct H1 as [y Hy]. destruct (D a) eqn:EQDa.
    * destruct (leq a a0) eqn:EQ1.
      ** destruct (leq a0 a) eqn:EQ2.
        *** exists y. now split.
        *** assert (exists z : X, (In z (build_sup_candidate_aux D lst cand) \/ z <= a) /\ x <= z).
            apply build_sup_domination_update_elim. exists y. apply Hy.
            destruct H1 as [z [Hz Hxz]]. destruct Hz. apply IHlst; try assumption. now exists z.
      
            pose proof (build_sup_preserves_domination D lst (a0::cand) x H). destruct H2 as [s [Hs Hxs]]. exists a0. split. apply in_eq.
            rewrite Hxz. rewrite H1. now apply Is_true_eq_left.
            now exists s.
      ** destruct (leq a0 a) eqn:EQ2.
        *** exists y. now split.
        *** apply IHlst; try assumption. exists y. now split.
    * apply IHlst; try assumption. exists y. now split.
 Qed.

Lemma main_invariant D : forall lst x, Is_true (D x) 
  -> ~ (In x lst) 
    \/ exists y, In y (build_sup_candidate_aux D lst nil) /\ x <= y.
Proof.
  induction lst.
  + intros. now left.
  + intros x Dx. pose proof (IHlst x Dx). apply Is_true_eq_true in Dx. destruct H.
    - destruct (eq_dec (projT2 X) a x).
      * right. cbn. destruct (D a) eqn:EQ. pose proof build_sup_preserves_domination. cbn in H0. apply H0.
        now apply Is_true_eq_left. exists a. split. apply in_eq. rewrite e. reflexivity.
        rewrite e in EQ. contradict Dx. now rewrite EQ.
      * left. intro. inversion H0; now contradict H1.
    - right. cbn. destruct (D a) eqn:EQ.
      * pose proof build_sup_domination_preserves_inclusion. cbn in H0. apply H0; try (now apply Is_true_eq_left). assumption.
      * apply H.
  Qed.

Lemma candidates_dominate_D D : forall x, Is_true (D x) -> exists y, In y (build_sup_candidate D) /\ x <= y.
 Proof.
  intros x Hx. destruct (main_invariant D (el (projT2 X)) x). assumption. contradict H. apply (all_el (projT2 X)).
  apply H.
 Qed.


  (** * There is at most one element in the list (zero if D is empty) *)

Lemma unique_candidate_if_directed D : is_true (Directed leq D) -> le (length (build_sup_candidate D)) 1.
Proof.
  intro HD.
  destruct (build_sup_candidate D) eqn:Sl. cbn. lia.
  destruct l eqn:Sl'. cbn. lia. exfalso.
  rewrite <- Directed_spec in HD. destruct (HD t t0) as [d [Hd [Htd Ht0d]]].
  apply candidates_are_in_D. rewrite Sl. apply in_eq.
  apply candidates_are_in_D. rewrite Sl. apply in_cons. apply in_eq.
  
  destruct (candidates_dominate_D D d) as [s [Hs Hds]]. assumption.
  
  destruct (candidates_are_incomparable D t t0) as [Htt0 | Htt0].
  rewrite Sl. apply in_eq. rewrite Sl. apply in_cons. apply in_eq.
  rewrite Htt0 in Sl. pose proof (candidates_have_no_duplicate D) as HF.
  rewrite Sl in HF. apply NoDup_cons_iff in HF. destruct HF as [HF _]. contradict HF. apply in_eq.
  
  rewrite Sl in Hs.  destruct Htt0 as [Htt0 Ht0t]. inversion Hs.
  contradict Ht0t. rewrite H. rewrite <- Hds. apply Ht0d.
  inversion H. contradict Htt0. rewrite H0. rewrite <- Hds. apply Htd.  
  
  destruct (candidates_are_incomparable D t s) as [Hts | Hts].
  rewrite Sl. apply in_eq. rewrite Sl. assumption.
  pose proof (candidates_have_no_duplicate D) as HF.
  rewrite Sl in HF. apply NoDup_cons_iff in HF. destruct HF as [HF _]. contradict HF.
  rewrite Hts. now apply in_cons.
  destruct Hts as [Hts Hst]. contradict Hts. rewrite <- Hds. apply Htd.
 Qed.



  (** * CPO of a finite partial order *)


Program Definition FinitePO_to_CPO : @B_CPO Bool_B X P' :=
  {| 
     sup D := hd bottom (build_sup_candidate D);
  |}.
Next Obligation.
  pose proof (unique_candidate_if_directed D (proj2_sig D)) as HL. destruct (build_sup_candidate D) eqn:Sl.
  + split; intros. destruct (candidates_dominate_D D y) as [d [Hd Hyd]]. assumption. rewrite Sl in Hd. contradict Hd.
    cbn. apply bottom_is_bot.
  + destruct l. cbn in *. split; intros.
    - destruct (candidates_dominate_D D y) as [sup [Hsup Hysup]]. assumption.
      rewrite Sl in Hsup. inversion Hsup. transitivity t. rewrite H1. apply Hysup. apply H. contradict H1.
    - apply H. apply candidates_are_in_D. rewrite Sl. apply in_eq.
    - contradict HL. cbn. lia.
 Qed.

End FiniteOrder.




Section Basic_CPOs.

(* ----- Defining Propositions as a CPO over Prop ----- *)

Program Definition Prop_valid_type := existT (fun P => True) Prop _.

Program Instance B_PO_Prop : @B_PO Prop_B Prop_valid_type :=
  {|
    weq P Q := P <-> Q;
    leq P Q := P -> Q;
  |}.
Next Obligation.
  apply Build_PreOrder.
  + now intros.
  + intros P Q R. tauto.
Qed.

Program Instance B_CPO_Prop : B_CPO B_PO_Prop :=
  {| 
     sup D := exists2 P, D P & P;
  |}.
Next Obligation. firstorder. Qed.

Program Instance B_Lattice_Prop : B_CPO B_PO_Prop :=
  {| 
     sup D := exists2 P, D P & P;
  |}.
Next Obligation. firstorder. Qed.


(* ----- Defining Booleans as a CPO over booleans ----- *)

 Program Definition leqb (b1 b2 : bool) := eqbool (X_fin := bool_fin) b1 false
                                         || eqbool (X_fin := bool_fin) b2 true.

Definition bool_valid_type := existT fin bool bool_fin.

Program Instance B_PO_bool : @B_PO Bool_B bool_valid_type :=
  {|
    weq x y := eqbool (X_fin := bool_fin) x y; (*leqb x y && leqb y x;*)
    leq := leqb;
  |}.
Next Obligation.
  apply Build_PreOrder.
  + intro x. destruct x; unfold leqb; apply orb_prop_intro; [right | left]; now apply eqbool_refl.
  + intros x y z Hxy Hyz. unfold leqb in *. apply orb_prop_intro. apply orb_prop_elim in Hxy, Hyz.
    destruct Hxy. now left. destruct Hyz. apply eqbool_refl in H, H0. rewrite H in H0. now contradict H0.
    now right.
Qed.
Next Obligation. split; intro H. apply eqbool_refl in H. rewrite H.
   split; now apply B_PO_bool_obligation_1.
   destruct x, y; try (now apply eqbool_refl); destruct H as [H1 H2];
   [apply orb_prop_elim in H1 as HF | apply orb_prop_elim in H2 as HF]; destruct HF as [HF | HF]; apply eqbool_refl in HF;
   now contradict HF.
Qed.

Program Instance B_CPO_bool : B_CPO B_PO_bool :=
  {| 
     sup D := D true;
  |}.
  Next Obligation. destruct z.
    split; intros; apply orb_prop_intro; right; now apply eqbool_refl.
    split.
    + intros Hsupz y HDy. destruct y; try (apply orb_prop_intro; left; now apply eqbool_refl).
      destruct (D true). apply orb_prop_elim in Hsupz. destruct Hsupz as [HF | HF];
      apply eqbool_refl in HF; now contradict HF. contradict HDy.
    + intro H. specialize H with true. destruct (D true). now apply H.
      apply orb_prop_intro. left. now apply eqbool_refl.
   Qed.
Program Instance B_Lattice_bool : B_CPO B_PO_bool :=
  {| 
     sup D := D true;
  |}.
  Next Obligation. destruct z.
    split; intros; apply orb_prop_intro; right; now apply eqbool_refl.
    split.
    + intros Hsupz y HDy. destruct y; try (apply orb_prop_intro; left; now apply eqbool_refl).
      destruct (D true). apply orb_prop_elim in Hsupz. destruct Hsupz as [HF | HF];
      apply eqbool_refl in HF; now contradict HF. contradict HDy.
    + intro H. specialize H with true. destruct (D true). now apply H.
      apply orb_prop_intro. left. now apply eqbool_refl.
   Qed.


End Basic_CPOs.



Section CPO_Examples.

Variant CPO_set : Type := bottom : CPO_set | x1 : CPO_set | x2 : CPO_set.

Program Definition CPO_fin : fin (CPO_set) := {| el := cons x2 (cons x1 (cons bottom nil)) |}.
Next Obligation. destruct a; destruct b; try (now left); try (right; intro; inversion H). Defined.
Next Obligation. destruct a; intuition. Defined.

Definition CPO_valid_type := existT fin CPO_set CPO_fin.


 Program Definition leq3 (x y : CPO_set) := eqbool (X_fin := CPO_fin) x y 
                                         || eqbool (X_fin := CPO_fin) x bottom 
                                         || eqbool (X_fin := CPO_fin) y x2.

Lemma or_to_orb : forall b1 b2 b3, Is_true (b1 || b2 || b3) <-> Is_true b1 \/ Is_true b2 \/ Is_true b3.
Proof. intros. split; intro H.
  + apply orb_prop_elim in H. destruct H. apply orb_prop_elim in H. intuition. intuition.
  + apply orb_prop_intro. destruct H. left. apply orb_prop_intro. now left.
    destruct H. left. apply orb_prop_intro. now right.
    now right.
Qed.

#[global]
Program Instance B_PO_ex : @B_PO Bool_B CPO_valid_type :=
  {|
    weq x y := leq3 x y && leq3 y x;
    leq := leq3;
  |}.
Next Obligation.
  apply Build_PreOrder.
  + intro x. unfold leq3. repeat (apply orb_prop_intro; left).
    unfold eqbool. now destruct (eq_dec CPO_fin x x).
  + intros x y z Hxy Hyz. unfold leq3 in *.
    rewrite or_to_orb in *. intuition.
    - left. now apply eqbool_trans with y.
    - apply eqbool_refl in H, H1. rewrite H. rewrite H1. right. left.
      now apply eqbool_refl.
    - apply eqbool_refl in H0, H1. rewrite <- H0. rewrite H1. right. right.
      now apply eqbool_refl.
    - apply eqbool_refl in H1, H. rewrite H1 in H. inversion H.
Qed.
Next Obligation. split. apply andb_prop_elim. apply andb_prop_intro. Qed.


Instance leq3_refl : Reflexive (fun x y => Is_true (leq3 x y)).
  Proof. apply B_PO_ex_obligation_1. Qed.

Instance leq3_trans : Transitive (fun x y => Is_true (leq3 x y)).
  Proof. apply B_PO_ex_obligation_1. Qed.


Lemma weq_is_eq : forall (x y : CPO_set), 
  @weq_in_prop Bool_B CPO_valid_type B_PO_ex x y <-> x = y.
 Proof. split; intro H. destruct x, y; easy. now rewrite H. Qed.
 
 Lemma weq_is_eq2 : forall (x y : CPO_set), 
  Is_true (@weq Bool_B CPO_valid_type B_PO_ex x y) <-> x = y.
 Proof. apply weq_is_eq. Qed.

Definition sup_ex (D :@directed_set Bool_B CPO_valid_type leq3) := if (D x2) then x2 else (
              if (D x1) then x1 else bottom).

 Program Instance B_CPO_ex : B_CPO B_PO_ex :=
  {| 
     sup D := sup_ex D;
  |}.
  Next Obligation.
    split.
    + intros Hsupz y HDy. transitivity (sup_ex D); try assumption.
      destruct y. unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      unfold sup_ex in *. destruct (D x2).
      unfold leq3. apply or_to_orb. right. right. now apply eqbool_refl.
      destruct (D x1). reflexivity. contradict HDy.
      unfold sup_ex in *. destruct (D x2). reflexivity. contradict HDy.
    
    + intros. unfold sup_ex. destruct z.
      - destruct (D x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (D x1) eqn:EQ1. apply Is_true_eq_left in EQ1. apply (H x1 EQ1).
        reflexivity.
      - destruct (D x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (D x1) eqn:EQ1. reflexivity.
        unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      - unfold leq3. apply or_to_orb. right. right. reflexivity.
   Qed.

 #[global]
 Program Instance B_Lattice_ex : B_CL B_PO_ex :=
  {|
    Sup D := if (D x2) then x2 else (
              if (D x1) then x1 else bottom);
  |}.
  Next Obligation.
  split.
    + intros Hsupz y HDy. transitivity (if Y x2 then x2 else if Y x1 then x1 else bottom); try assumption.
      destruct y. unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      unfold sup_ex in *. destruct (Y x2).
      unfold leq3. apply or_to_orb. right. right. now apply eqbool_refl.
      destruct (Y x1). reflexivity. contradict HDy.
      unfold sup_ex in *. destruct (Y x2). reflexivity. contradict HDy.
    
    + intros. unfold sup_ex. destruct z.
      - destruct (Y x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (Y x1) eqn:EQ1. apply Is_true_eq_left in EQ1. apply (H x1 EQ1).
        reflexivity.
      - destruct (Y x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (Y x1) eqn:EQ1. reflexivity.
        unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      - unfold leq3. apply or_to_orb. right. right. reflexivity.
  Defined.



  Program Definition F : CPO_set -> CPO_set := fun x => match x with
      | bottom => x2
      | x1 => x1
      | x2 => x2
    end.
 
  Lemma Increasing_F : is_true (@Increasing Bool_B CPO_valid_type B_PO_ex F).
  Proof. unfold Increasing. rewrite <- BForall_spec. intro x. destruct x; cbn; constructor. Qed.
 
 Definition P0_ex := (@P0 Bool_B CPO_valid_type B_PO_ex B_CPO_ex F).
 
 Definition P0' : (CPO_set -> bool) := fun x => (eqbool (X_fin := CPO_fin) x bottom || eqbool (X_fin := CPO_fin) x x2).
 
 Lemma P0'_is_invariant_subCPO : is_true (@Invariant Bool_B CPO_valid_type B_PO_ex F P0')
                              /\ is_true (@is_subCPO Bool_B CPO_valid_type B_PO_ex B_CPO_ex P0').
 Proof. split.
  + unfold Invariant. rewrite included_spec. intros x Hx. destruct x.
    unfold P0'. apply orb_prop_intro. now left. inversion Hx.
    unfold Image in Hx. rewrite <- BExists_spec in Hx. destruct Hx. rewrite <- BAnd_spec in H.
    destruct H as [HPx Hx2x]. rewrite weq_is_eq2 in Hx2x. rewrite Hx2x.
    destruct x; try easy.
  + apply is_subCPO_spec. intros D HDP. rewrite included_spec in HDP.
    cbn. unfold sup_ex. destruct (D x2) eqn:EQ.
    - setoid_rewrite EQ. apply HDP. now apply Is_true_eq_left in EQ.
    - setoid_rewrite EQ. destruct (D x1) eqn:EQ1. apply Is_true_eq_left in EQ1.
      pose proof (HDP x1 EQ1). contradict H.
      setoid_rewrite EQ1. easy.
  Qed.

 Lemma P0_is_P0' : is_true (@set_eq Bool_B CPO_valid_type P0_ex P0').
 Proof. unfold set_eq. apply BForall_spec. intro. apply BEq_spec. split; intro.
  + unfold P0_ex in H. rewrite <- P0_spec in H. apply (H P0'); try apply P0'_is_invariant_subCPO.
    intros. apply weq_is_eq in H0. now rewrite H0.
  + destruct x; unfold P0_ex; apply P0_spec.
    - intros Y Hi Hs HProper. rewrite <- is_subCPO_spec in Hs. apply (Hs empty). intuition.
    - inversion H.
    - intros Y Hi Hs HProper. unfold Invariant in Hi. rewrite included_spec in Hi.
      apply Hi. replace x2 with (F bottom). unfold Image. rewrite <- BExists_spec.
      exists bottom. rewrite <- BAnd_spec. split. rewrite <- is_subCPO_spec in Hs. now apply (Hs empty).
      reflexivity. now cbn.
  Qed.
  
  Lemma top_of_P0_is_x2 : Sup P0_ex = x2.
  Proof. simpl. destruct (P0_ex x2) eqn:EQ. reflexivity. exfalso.
    pose proof P0_is_P0'. unfold set_eq in H. rewrite <- BForall_spec in H. 
    specialize H with x2. rewrite <- BEq_spec in H. contradict EQ. 
    assert (P0_ex x2 = true). apply Is_true_eq_true. now apply H.
    rewrite H0. easy.
  Qed.
  
  Lemma top_of_P0_is_not_minimal : exists (a : CPO_set), is_greatest P0_ex a 
                                                      /\ ~ (is_least (@Fix Bool_B CPO_valid_type B_PO_ex F) a).
  Proof.
  exists (Sup P0_ex). split.
  + split.
      - rewrite top_of_P0_is_x2. pose proof P0_is_P0'. unfold set_eq in H. rewrite <- BForall_spec in H. 
        specialize H with x2. rewrite <- BEq_spec in H. now apply H. 
      - intros. now eapply leq_xSup.
    + intro. destruct H.
      rewrite top_of_P0_is_x2 in H0. specialize H0 with x1.
      assert (@is_true Bool_B (leq3 x2 x1)). apply H0. now cbn. inversion H1.
  Qed.
  
  
  
  (* ----- Testing computation of a minimal fixpoint ----- *)

  Program Definition Fmon : @mon Bool_B CPO_valid_type B_PO_ex := fun x => match x with
      | bottom => x1
      | x1 => x1
      | x2 => x2
    end.

Goal True.
set (x := @lfp_II Bool_B CPO_valid_type B_PO_ex B_CPO_ex Fmon).
(*simpl in x. unfold sup_ex in x.*) vm_compute in x.
(*Eval cbv in @gfp_II Bool_B CPO_valid_type B_PO_ex B_CPO_ex Fmon.*)
easy.
Qed.

  Program Definition id_P : @mon Prop_B _ B_PO_Prop := id.
  Goal True.
  set (x := @lfp_II Prop_B _ B_PO_Prop B_CPO_Prop id_P).
  vm_compute in x.
  easy.
  Qed.

End CPO_Examples.




Section CPO_based_Truth_values.

 Notation top := x2.
 Notation unknown := x1.
 
 (* Ensemble à trois éléments, valeur de vérité Unknown ou top*)
 
 Definition imply x1 x2 := match x1,x2 with
    | bottom, _ => top
    | _, top => top
    | unknown, unknown => top
    | top, unknown => unknown
    | unknown, bottom => bottom
    | top, bottom => bottom
  end.
 
 Program Instance CPO_B_True : B_param :=
  {|
    B := CPO_set;
    K := @K Bool_B;
    is_true x := is_true (leq (B_PO := B_PO_ex) unknown x);
    BFalse := @Bot Bool_B CPO_valid_type B_PO_ex B_Lattice_ex;
    BTrue := top;
    BAnd := (@cap Bool_B CPO_valid_type B_PO_ex B_Lattice_ex);
    BOr := (@cup Bool_B CPO_valid_type B_PO_ex B_Lattice_ex);
    BImpl := imply;
    BForall V := fun P => Inf (fun x => BExists V (fun v => (weq x (P v))));
    BExists V := fun P => Sup (fun x => BExists V (fun v => (weq x (P v))));
  |}.
  Next Obligation. now destruct b1, b2. Qed.
  Next Obligation. destruct b1, b2; intuition. Qed.
  Next Obligation. destruct b1, b2; intuition. Qed.
  Next Obligation. exists (el (@funP A X _)). apply (eq_dec (@funP A X _)).
   apply (all_el (@funP A X _)). Defined.
  Next Obligation. exists (el (@funAB A B X X0)). apply (eq_dec (@funAB A B X X0)).
   apply (all_el (@funAB A B X X0)). Defined.
  Next Obligation. exists (el (@funAB A _ X CPO_fin)). apply (eq_dec (@funAB A _ X CPO_fin)).
   apply (all_el (@funAB A _ X CPO_fin)). Defined.
  Next Obligation. cbn in *.
    split; intro Q. 
    + destruct (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X)) eqn:EQ1; cbn;
      destruct (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X)) eqn:EQ2; cbn;
      destruct (existsb (fun v : V => leq3 bottom (P v) && leq3 (P v) bottom) (el X)) eqn:EQ3; cbn; try auto;
      rewrite existsb_exists in EQ3; destruct EQ3 as [x [Xx Hx]]; specialize Q with x; now destruct (P x).
    + destruct (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X)) eqn:EQ1; cbn in *;
      destruct (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X)) eqn:EQ2; cbn in *;
      destruct (existsb (fun v : V => leq3 bottom (P v) && leq3 (P v) bottom) (el X)) eqn:EQ3; cbn in *;
      try (now contradict Q);
        intro x; destruct (P x) eqn:EQ; try auto; contradict EQ3; 
        assert (existsb (fun v : V => leq3 bottom (P v) && leq3 (P v) bottom) (el X) = true) as H;
        try (rewrite existsb_exists; exists x; split); try apply all_el; try (now rewrite EQ);
        now rewrite H.
  Qed.
  Next Obligation. cbn in *.
    destruct (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X)) eqn:EQ1; cbn in *;
    destruct (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X)) eqn:EQ2; cbn in *;
    intuition.
    + apply existsb_exists in EQ2. destruct EQ2 as [x [Xx Hx]].
      apply Is_true_eq_left in Hx. apply andb_prop_elim in Hx. exists x. apply Hx.
    + apply existsb_exists in EQ1. destruct EQ1 as [x [Xx Hx]].
      apply Is_true_eq_left in Hx. apply andb_prop_elim in Hx. exists x.
      destruct (P x); try (now contradict Hx). auto.
    + apply existsb_exists in EQ2. destruct EQ2 as [x [Xx Hx]].
      apply Is_true_eq_left in Hx. apply andb_prop_elim in Hx. exists x. apply Hx.
    + destruct H as [x Hx]. destruct (P x) eqn:EQ. contradict Hx. contradict EQ2.
      assert (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X) = true).
      apply existsb_exists. exists x. split. apply all_el. rewrite EQ. now cbn. now rewrite H.
      contradict EQ1. assert (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X) = true).
      apply existsb_exists. exists x. split. apply all_el. now rewrite EQ. now rewrite H.
  Qed.


(* Same but only top is true *)
 Definition imply' x1 x2 := match x1,x2 with
    | bottom, _ => top
    | _, top => top
    | unknown, unknown => top
    | top, unknown => unknown
    | unknown, bottom => top (*RMQ : c'est très intéressant ici, 
    la seule valeur qui marche et respecte la spécification de l'implication c'est top.
    Ca correspond à l'intuition, les valeurs sont toutes réduites à leur identification à
    vrai ou faux, et indistinguable de ces derniers !
    (Parce que c'est pas logique que unknown -> bot soit vrai, sauf si unknown est forcément faux.*)
    | top, bottom => bottom
  end.

Program Instance CPO_B_False : B_param :=
  {|
    B := CPO_set;
    K := @K Bool_B;
    is_true x := is_true (leq (B_PO := B_PO_ex) top x);
    BFalse := @Bot Bool_B CPO_valid_type B_PO_ex B_Lattice_ex;
    BTrue := top;
    BAnd := (@cap Bool_B CPO_valid_type B_PO_ex B_Lattice_ex);
    BOr := (@cup Bool_B CPO_valid_type B_PO_ex B_Lattice_ex);
    BImpl := imply';
    BForall V := fun P => Inf (fun x => BExists V (fun v => (weq x (P v))));
    BExists V := fun P => Sup (fun x => BExists V (fun v => (weq x (P v))));
  |}.
  Next Obligation. now destruct b1, b2. Qed.
  Next Obligation. destruct b1, b2; intuition. Qed.
  Next Obligation. destruct b1, b2; intuition. Qed.
  Next Obligation. exists (el (@funP A X _)). apply (eq_dec (@funP A X _)).
   apply (all_el (@funP A X _)). Defined.
  Next Obligation. exists (el (@funAB A B X X0)). apply (eq_dec (@funAB A B X X0)).
   apply (all_el (@funAB A B X X0)). Defined.
  Next Obligation. exists (el (@funAB A _ X CPO_fin)). apply (eq_dec (@funAB A _ X CPO_fin)).
   apply (all_el (@funAB A _ X CPO_fin)). Defined.
  Next Obligation. cbn in *.
    split; intro Q.
    + destruct (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X)) eqn:EQ1; cbn;
      destruct (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X)) eqn:EQ2; cbn;
      destruct (existsb (fun v : V => leq3 bottom (P v) && leq3 (P v) bottom) (el X)) eqn:EQ3; cbn; try auto;
      try (rewrite existsb_exists in EQ3; destruct EQ3 as [x [Xx Hx]]; specialize Q with x; now destruct (P x));
      rewrite existsb_exists in EQ2; destruct EQ2 as [x [Xx Hx]]; specialize Q with x; now destruct (P x).
    + destruct (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X)) eqn:EQ1; cbn in *;
      destruct (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X)) eqn:EQ2; cbn in *;
      destruct (existsb (fun v : V => leq3 bottom (P v) && leq3 (P v) bottom) (el X)) eqn:EQ3; cbn in *;
      try (now contradict Q).
      -  intro x; destruct (P x) eqn:EQ; try auto. contradict EQ3; 
        assert (existsb (fun v : V => leq3 bottom (P v) && leq3 (P v) bottom) (el X) = true) as H;
        try (rewrite existsb_exists; exists x; split); try apply all_el; try (now rewrite EQ);
        now rewrite H.
        contradict EQ2; 
        assert (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X) = true) as H;
        try (rewrite existsb_exists; exists x; split); try apply all_el; try (now rewrite EQ);
        now rewrite H.
     - intro x; destruct (P x) eqn:EQ; try auto. contradict EQ3; 
        assert (existsb (fun v : V => leq3 bottom (P v) && leq3 (P v) bottom) (el X) = true) as H;
        try (rewrite existsb_exists; exists x; split); try apply all_el; try (now rewrite EQ);
        now rewrite H.
        contradict EQ2; 
        assert (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X) = true) as H;
        try (rewrite existsb_exists; exists x; split); try apply all_el; try (now rewrite EQ);
        now rewrite H.
  Qed.
  Next Obligation. cbn in *.
    destruct (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X)) eqn:EQ1; cbn in *;
    destruct (existsb (fun v : V => leq3 unknown (P v) && leq3 (P v) unknown) (el X)) eqn:EQ2; cbn in *;
    intuition;
      try (apply existsb_exists in EQ1; destruct EQ1 as [x [Xx Hx]];
      apply Is_true_eq_left in Hx; apply andb_prop_elim in Hx; exists x; apply Hx);
      assert (existsb (fun v : V => leq3 top (P v) && leq3 (P v) top) (el X) = true);
      try (apply existsb_exists; destruct H as [x Hx]; exists x; split; try (apply all_el); now destruct (P x));
      contradict EQ1; now rewrite H0.
   Qed.

(*
 Context {X : valid_type (B_param := Bool_B)} {L' : B_PO (B := Bool_B) (X := X)} 
  {Xfin_CL : B_CL L'}.
 Hypothesis no_unique_valued_logic : ~ (weq_in_prop (B := Bool_B) Bot Top).


 Program Instance CPO_B : B_param :=
  {|
    B := X;
    K := @K Bool_B;
    is_true x := is_true (weq (B_PO := L') x Top);
    BFalse := Bot; (*@Bot Bool_B CPO_valid_type B_PO_ex B_Lattice_ex;*)
    BTrue := Top;
    BAnd := cap;
    BOr := cup;
    BImpl x1 x2 := Sup (fun x => leq (cap x1 x) x2); (*cf algèbres de Heyting*)
    
    BForall V := fun P => Inf (fun x => BExists V (fun v => (weq x (P v))));
    BExists V := fun P => Sup (fun x => BExists V (fun v => (weq x (P v))));
  |}.
  Next Obligation. split; intro H.
    + destruct H as [Hb1 Hb2]. apply (weq_spec (B_PO := L')). split. apply Top_spec.
      apply cap_spec. split. apply (weq_spec (B_PO := L')) in Hb1. apply Hb1.
      apply (weq_spec (B_PO := L')) in Hb2. apply Hb2.
    + apply (weq_spec (B_PO := L')) in H. destruct H as [Hleq Hgeq].
      apply cap_spec in Hgeq. split; apply (weq_spec (B_PO := L')); split; try apply Top_spec; apply Hgeq.
  Qed.
  Next Obligation. split; intro H.
    + apply (weq_spec (B_PO := L')). split. apply Top_spec.
      destruct H; apply (weq_spec (B_PO := L')) in H. transitivity b1.
      apply H. apply cup_l. transitivity b2. apply H. apply cup_r.
    + (* FAUX ! Ceci ne serait vrai que si on travaille dans une chaîne, ou dans Prop. *)
  Qed.
  
  *)

End CPO_based_Truth_values.

(*
Lemma notnotand : forall P Q, ~~ (P /\ Q) <-> ~~ P /\ ~~ Q.
Proof. tauto. Qed.

Lemma notnotimpl : forall (P Q : Prop), ~~ (P -> Q) <-> (~~ P -> ~~ Q).
Proof. tauto. Qed.

Lemma notnotor : forall P Q, ~~ (P \/ Q)  -> ~~ (~~ P \/ ~~ Q).
Proof. intuition. Qed.

Lemma test : forall (P Q R : Prop), (P \/ Q ->  R) <-> ((P -> R) /\ (Q -> R)).
Proof. tauto. Qed.
*)