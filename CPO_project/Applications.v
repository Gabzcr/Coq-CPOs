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
  |}.


Program Definition bool_fin : fin bool := {| el := cons true (cons false nil) |}.
Next Obligation. destruct a; destruct b. now left. now right. now right. now left. Qed.
Next Obligation. destruct a. now left. right. now left. Qed.


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
 
 Definition incomparable l := forall x y, In x l -> In y l -> (x = y) \/ (~ x <= y /\ ~ y <= x).
 
 Lemma included_stays_incomparable : forall l a, incomparable (a::l) -> incomparable l.
 Proof. unfold incomparable. intros. apply H; now apply in_cons. Qed.
 
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
  
 (* TODO *)
 
 Program Definition build_sup_candidate (D : X -> bool) :=
  build_sup_candidate_aux D (el (projT2 X)) nil (*(cons bottom nil)*).
  
  
  
 Lemma update_contains_bigger : forall el cand, exists el0, In el0 (update_candidates el cand) /\ el <= el0.
 Proof.
 induction cand.
 + exists el. split. cbn. now left. reflexivity.
 + cbn. destruct (leq a el) eqn:EQ1. apply IHcand. destruct (leq el a) eqn:EQ2. exists a.
  split. apply in_eq. now apply Is_true_eq_left. cbn. destruct IHcand as [x [Hx1 Hx2]].
  exists x. split. now right. apply Hx2.
 Qed.
 
 Lemma update_adds_el_and_retrieve_others : forall el l x, In x (update_candidates el l) ->
  In x l \/ (x = el).
 Proof. induction l.
 + cbn. intros. destruct H. now right. now left.
 + intros. cbn in *. destruct (leq a el). destruct (IHl x). assumption.
  left. now right. now right. destruct (leq el a). inversion H. left. now left.
  left. now right. inversion H. left. now left. destruct (IHl x). assumption. left. now right.
  now right.
 Qed.
 
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
 
 Fixpoint list_eq (l1 l2 : list X) := match l1,l2 with
  | nil, nil => True
  | nil,_ => False
  | _, nil => False
  | (h1::q1), (h2::q2) => (h1 == h2) /\ list_eq q1 q2
  end.
 
 
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
    
  
  (*
   cbn. destruct (leq a y) eqn:EQay.
    - destruct (leq a x)eqn:EQax. cbn in IHl. apply IHl.
      destruct (leq x a) eqn:EQxa. split. intro.
    
    
    apply Is_true_eq_left in EQxy, EQyx. cbn. split.
    assert (is_true (weq x y)). apply weq_spec. now split. apply H. easy.
    cbn. now split.
    destruct (leq y x)eqn:EQyx. cbn. now split.
*)
 


 Lemma test0 D : forall lst cand x, Is_true (D x) -> (*In x cand -> *)
  (exists y, In y cand /\ x <= y) ->
  exists y, In y (build_sup_candidate_aux D lst cand) /\ x <= y.
 Proof.
  induction lst.
  + intros cand x Dx Hx. cbn. apply Hx.
  + intros cand x Dx Hx. cbn in *. destruct (D a) eqn:EQ.
    - apply IHlst. assumption. pose proof update_preserves_domination. cbn in H. now apply H.
    - now apply IHlst.
 Qed.

(*
   Lemma test0' D : forall lst cand x, Is_true (D x) -> (*In x cand -> *)
  (exists y, In y (build_sup_candidate_aux D lst cand) /\ x <= y) ->
  (exists y, In y cand /\ x <= y).
 Proof.
  induction lst.
  + intros. cbn. apply H0.
  + intros cand x Dx Hx. cbn in *. destruct (D a) eqn:EQ.
    - apply IHlst. assumption. pose proof (update_preserves_domination a cand x). apply H in Hx. cbn in H. apply H.
    - now apply IHlst.
 Qed.
*)

  Lemma build_sup_candidate_aux_preserves_property D lst x : forall cand1 cand2,
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


(*
Lemma test1' D : forall lst cand x f, (forall l z, In z l  -> In z (f l))
  -> (exists y, In y (build_sup_candidate_aux D lst cand) /\ x <= y)
  -> (exists y, In y (build_sup_candidate_aux D lst (f cand)) /\ x <= y).
 Proof.
  intros. destruct H0 as [y [Hy Hxy]].
  
  
   induction lst.
  + cbn in *. exists y. split. now right. assumption.
  +
*)

 Lemma test3 : forall x y cand, (~ x <= y /\ ~ y <= x) -> (In x cand <-> In x (update_candidates y cand)).
 Proof.
  intros. induction cand.
  + cbn. split; intro. contradict H0. destruct H0. destruct H. contradict H. now rewrite H0. assumption.
  + split; intro.
    - inversion H0.
      * cbn. destruct (leq a y) eqn:EQ. destruct H as [Hxy Hyx]. contradict Hxy.
        rewrite H1 in EQ. now apply Is_true_eq_left. destruct (leq y a) eqn:EQ2. assumption. rewrite H1. apply in_eq.
      * cbn. destruct (leq a y) eqn:EQ. now apply IHcand.
        destruct (leq y a)eqn:EQ2. assumption. apply in_cons. now apply IHcand.
    - cbn in H0. destruct (leq a y). apply in_cons. now apply IHcand. destruct (leq y a). assumption.
      inversion H0. rewrite H1. apply in_eq. apply in_cons. now apply IHcand.
 Qed.
    
 (*
 Lemma test2 D : forall lst cand x y, (~ x <= y /\ ~ y <= x) -> 
  (exists z, In z (build_sup_candidate_aux D lst (update_candidates y cand)) /\ x <= z)
  -> exists z, In z (build_sup_candidate_aux D lst cand) /\ x <= z.
 Proof.
  induction lst.
  + intros. cbn in H0. cbn. destruct H0 as [z [Hz Hxz]]. exists z. pose proof (test3 z y cand).
    split. rewrite H0. assumption. split. intro. destruct H. contradict H. rewrite <- H1. apply Hxz. intro.
    destruct H. contradict H1. (*
  + intros. cbn. cbn in H0. destruct (D a).
  
    assert (forall l, (update_candidates a (update_candidates y l)) = (update_candidates y (update_candidates a l))).
    admit.
    rewrite H1 in H0. apply IHlst with y. apply H. assumption. apply IHlst with y. apply H. assumption.*)
  Admitted.*)
  
 Lemma test2' D : forall lst cand x y,
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
        pose proof build_sup_candidate_aux_preserves_property as RW. 
        specialize RW with D lst x (update_candidates y (update_candidates a cand)) 
                                   (update_candidates a (update_candidates y cand)).
        apply RW. apply In_update_is_commutative. clear RW. apply H.
      * apply IHlst. apply H.
  Qed.


 Lemma test1 D : forall lst cand x a, Is_true (D x) -> Is_true (D a) ->
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
            apply test2'. exists y. apply Hy.
            destruct H1 as [z [Hz Hxz]]. destruct Hz. apply IHlst; try assumption. now exists z.
      
            pose proof (test0 D lst (a0::cand) x H). destruct H2 as [s [Hs Hxs]]. exists a0. split. apply in_eq.
            rewrite Hxz. rewrite H1. now apply Is_true_eq_left.
            now exists s.
      ** destruct (leq a0 a) eqn:EQ2.
        *** exists y. now split.
        *** apply IHlst; try assumption. exists y. now split.
    * apply IHlst; try assumption. exists y. now split.
 Qed.
    
    (*
    exists a0. split. pose proof test0. apply test0.
    
    
    exists y. now split.
    destruct (leq a0 a) eqn:EQ2. apply IHlst.
 
 
 
  intros. destruct H1 as [y [Hy Hxy]]. destruct (leq y a) eqn:EQ.
  + destruct (test0 D lst (a::cand) a) as [z Hz]. assumption. exists a.
    split. apply in_eq. reflexivity.
    exists z. split. apply Hz. destruct Hz as [_ Hz]. rewrite <- Hz. rewrite Hxy.
    now apply Is_true_eq_left.
  
  + assert (exists y, In y (build_sup_candidate_aux D lst cand) /\ x <= y).
    now exists y. clear Hy. clear Hxy. clear EQ. clear y.
    induction lst.
    - cbn in *. destruct H1 as [y Hy]. exists y. split. now right. apply Hy.
    - cbn in *. destruct H1 as [y Hy]. destruct (D a0). destruct (leq a a0) eqn:EQ1.
      destruct (leq a0 a) eqn:EQ2. exists y. now split.
      exists y. now split.
      destruct (leq a0 a) eqn:EQ2. apply IHlst.
  Admitted.*)
      (*TODO*)
    
    (*
  + exists y. split; try assumption. induction lst.
    - cbn in *. now right.
    - cbn in *. destruct (D a0). destruct (leq a a0) eqn:EQ1. apply Hy.
      destruct (leq a0 a) eqn:EQ2. apply IHlst. (*apply Hy*)
      *)
    (*
    induction lst.
  + cbn in *. exists y. split. now right. assumption.
  + cbn in *. destruct (D a0) eqn:EQ. destruct (leq a a0) eqn:EQ1. now exists y.
    destruct (leq a0 a). apply IHlst. admit. (*TODO false here, change condition*) *)


Lemma invariant D : forall lst x, Is_true (D x) 
  -> ~ (In x lst) 
    \/ exists y, In y (build_sup_candidate_aux D lst nil) /\ x <= y.
Proof.
  induction lst.
  + intros. now left.
  + intros x Dx. pose proof (IHlst x Dx). apply Is_true_eq_true in Dx. destruct H.
    - destruct (eq_dec (projT2 X) a x).
      * right. cbn. destruct (D a) eqn:EQ. pose proof test0. cbn in H0. apply H0.
        now apply Is_true_eq_left. exists a. split. apply in_eq. rewrite e. reflexivity.
        rewrite e in EQ. contradict Dx. now rewrite EQ.
      * left. intro. inversion H0; now contradict H1.
    - right. cbn. destruct (D a) eqn:EQ.
      * pose proof test1. cbn in H0. apply H0; try (now apply Is_true_eq_left). assumption.
      * apply H.
  Qed.

Lemma candidates_dominate_D D : forall x, Is_true (D x) -> exists y, In y (build_sup_candidate D) /\ x <= y.
 Proof.
  intros x Hx. destruct (invariant D (el (projT2 X)) x). assumption. contradict H. apply (all_el (projT2 X)).
  apply H.
 Qed.
  

(*
Lemma invariant D lst cand : (forall x, Is_true (D x) -> In x lst \/ exists y, In y cand /\ x <= y)
  -> (forall x, Is_true (D x) -> exists y, In y (build_sup_candidate_aux D lst cand) /\ x <= y).
 Proof.
  intro H. induction lst.
  + intros x Dx. cbn. destruct (H x). assumption. contradict H0. assumption.
  + intros x Dx. destruct (H x). assumption. admit.
    cbn. destru 
    
    
  induction lst.
  + intros H x Dx. cbn. destruct (H x). assumption. contradict H0. assumption.
  + intros H x Dx. destruct (H x). assumption. admit.
    cbn. destru 
*)

(*
Lemma invariant D (* build sup aux preserves this property : *): forall a lst cand, forall x, Is_true (D a) ->
  (In x lst -> (exists d, In d (build_sup_candidate_aux D lst cand) /\ x <= d))
  -> (In x (a::lst) -> (exists d, In d (build_sup_candidate_aux D (a::lst) (update_candidates a cand)) /\ x <= d)).
 Proof.
  intros. cbn. destruct (D a).
  
  contradict H.
 Qed.
*)


(*
Lemma invariant D : forall lst x, In x lst -> (exists d, In d (build_sup_candidate_aux D lst nil) /\ x <= d).
Proof.
  induction lst.
  + intros. contradict H.
  + intros x Hx. inversion Hx. cbn.
    destruct (D a). destruct (update_contains_bigger a (a::nil)).
    exists x0. rewrite <- H. split. cbn.
  
    destruct (IHlst x H) as [d [HDlst Hxd]]. exists d. split.
    - cbn. destruct (D a). admit.
      (* TODO : lemme, l1 inclus dans l2 implique que build_sup l1 inclus and build_sup l2*)
       assumption.
    - assumption.
Qed.*)

(*
 Lemma build_sup_contains_maximal_elements D :
  forall lst cand (d : X), 
    (forall d', In d' cand -> (forall x, Is_true (D x) -> (x <= d' \/ In x lst))) ->
    In d (build_sup_candidate_aux D lst cand) -> 
    (forall x, Is_true (D x) -> (x <= d \/ In x lst)).
 Proof.
   induction lst.
   + intros. cbn in *. now apply H.
   + intros. 
 
 
 
  induction lst.
  + intros. cbn in H. contradict H.
  +
  
 
  unfold build_sup_candidate. induction (el (projT2 X)) eqn:EQ.
  + intros. contradict H.
  + assert (forall lst cand d, In d (build_sup_candidate_aux D lst cand) 
    -> (forall x, Is_true (D x) -> x <= d \/ In x lst)).
*)

(*
 Lemma build_sup_contains_sup (D : directed_set leq) : 
  forall (d x : X), List.In d (build_sup_candidate D) -> is_true (D x) -> is_true (leq x d).
 Proof.
  unfold build_sup_candidate. induction (el (projT2 X)).
  + intros. contradict H.
  + intros d x Hd. cbn in Hd. destruct (D a) eqn:EQ.
    induction l.
    - cbn in *. destruct Hd. rewrite H.
    unfold build_sup_candidate_1_step in Hd.
*)




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


Lemma candidates_have_no_duplicate_aux D cand lst : 
  NoDup cand -> NoDup (build_sup_candidate_aux D lst cand).
 Proof.
  revert cand. induction lst. intro. unfold build_sup_candidate.
  + now cbn.
  + cbn. destruct (D a) eqn:EQDa. 
    - intros. apply IHlst. now apply update_preserves_NoDup.
     - apply IHlst.
  Qed.

Lemma candidates_have_no_duplicate D : NoDup (build_sup_candidate D).
Proof. apply candidates_have_no_duplicate_aux. constructor. Qed.
  

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


(* TODO : montrer que la tête de la liste des candidats sup est bien un sup (i.e. tout le monde est sous lui) *)

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

(* TODO : montrer que tout ordre partiel FINI est un CPO *)

End CPO_Examples.
