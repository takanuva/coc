Require Import Arith.
Require Import Compare_dec.
Require Import Relations.
Require Import Extraction.

Inductive pseudoterm: Set :=
  | type
  | prop
  | bound (n: nat)
  | pi (t: pseudoterm) (b: pseudoterm)
  | lambda (t: pseudoterm) (b: pseudoterm)
  | application (f: pseudoterm) (x: pseudoterm).

Hint Constructors pseudoterm: coc.

Bind Scope coc_scope with pseudoterm.
Notation "*" := (prop): coc_scope.
Notation "\ t , b" := (lambda t b) (at level 190, format "\ t ,  b"): coc_scope.
Notation "\/ t , b" := (pi t b) (at level 190, format "\/ t ,  b"): coc_scope.
Notation "f @ x" := (application f x) (at level 150): coc_scope.
Coercion bound: nat >-> pseudoterm.

Inductive subterm: pseudoterm -> pseudoterm -> Prop :=
  | subterm_pi_left:
    forall t b, subterm t (pi t b)
  | subterm_pi_right:
    forall t b, subterm b (pi t b)
  | subterm_lambda_left:
    forall t b, subterm t (lambda t b)
  | subterm_lambda_right:
    forall t b, subterm b (lambda t b)
  | subterm_application_left:
    forall f x, subterm f (application f x)
  | subterm_application_right:
    forall f x, subterm x (application f x).

Hint Constructors subterm: coc.

Fixpoint lift (i: nat) (k: nat) (e: pseudoterm): pseudoterm :=
  match e with
  | type =>
    type
  | prop =>
    prop
  | bound n =>
    match le_gt_dec k n with
    | left _ => bound (i + n)
    | right _ => bound n
    end
  | pi t b =>
    pi (lift i k t) (lift i (S k) b)
  | lambda t b =>
    lambda (lift i k t) (lift i (S k) b)
  | application f x =>
    application (lift i k f) (lift i k x)
  end.

Lemma lift_zero_e_equals_e:
  forall e k,
  lift 0 k e = e.
Proof.
  induction e.
  - trivial.
  - trivial.
  - intro; unfold lift.
    destruct (le_gt_dec k n); reflexivity.
  - unfold lift in * |- *; intro.
    rewrite (IHe1 k).
    rewrite (IHe2 (S k)).
    reflexivity.
  - unfold lift in * |- *; intro.
    rewrite (IHe1 k).
    rewrite (IHe2 (S k)).
    reflexivity.
  - unfold lift in * |- *; intro.
    rewrite (IHe1 k).
    rewrite (IHe2 k).
    reflexivity.
Defined.

Fixpoint subst (p: pseudoterm) (k: nat) (q: pseudoterm): pseudoterm :=
  match q with
  | type =>
    type
  | prop =>
    prop
  | bound n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => bound (pred n)
    | inleft (right _) => lift k 0 p
    | inright _ => bound n
    end
  | pi t b =>
    pi (subst p k t) (subst p (S k) b)
  | lambda t b =>
    lambda (subst p k t) (subst p (S k) b)
  | application f x =>
    application (subst p k f) (subst p k x)
  end.

Notation "q [ p /]" := (subst p 0 q) (at level 1, format "q [ p /]"): coc_scope.

Inductive step: pseudoterm -> pseudoterm -> Prop :=
  | step_beta:
    forall t b x,
    step ((\t, b) @ x) (b[x/])
  | step_pi_left:
    forall t1 t2 b,
    step t1 t2 -> step (\/t1, b) (\/t2, b)
  | step_pi_right:
    forall t b1 b2,
    step b1 b2 -> step (\/t, b1) (\/t, b2)
  | step_lambda_left:
    forall t1 t2 b,
    step t1 t2 -> step (\t1, b) (\t2, b)
  | step_lambda_right:
    forall t b1 b2,
    step b1 b2 -> step (\t, b1) (\t, b2)
  | step_application_left:
    forall f1 f2 x,
    step f1 f2 -> step (f1 @ x) (f2 @ x)
  | step_application_right:
    forall f x1 x2,
    step x1 x2 -> step (f @ x1) (f @ x2).

Hint Constructors step: coc.
Notation "[ a => b ]" := (step a b): type_scope.

Definition star: pseudoterm -> pseudoterm -> Prop :=
  clos_refl_trans _ step.

Hint Unfold star: coc.
Hint Constructors clos_refl_trans: coc.
Notation "[ a =>* b ]" := (star a b): type_scope.

Lemma star_beta:
  forall t b x,
  [(\t, b) @ x =>* b[x/]].
Proof.
  auto with coc.
Defined.

Hint Resolve star_beta: coc.

Lemma star_step:
  forall a b, [a => b] -> [a =>* b].
Proof.
  auto with coc.
Defined.

Hint Resolve star_step: coc.

Lemma star_symm:
  forall a, [a =>* a].
Proof.
  auto with coc.
Defined.

Hint Resolve star_symm: coc.

Lemma star_tran:
  forall a b c, [a =>* b] -> [b =>* c] -> [a =>* c].
Proof.
  intros.
  eauto with coc.
Defined.

Hint Resolve star_tran: coc.

Lemma star_pi_left:
  forall t1 t2 b,
  [t1 =>* t2] -> [\/t1, b =>* \/t2, b].
Proof.
  induction 1; eauto with coc.
Defined.

Hint Resolve star_pi_left: coc.

Lemma star_pi_right:
  forall t b1 b2,
  [b1 =>* b2] -> [\/t, b1 =>* \/t, b2].
Proof.
  induction 1; eauto with coc.
Defined.

Hint Resolve star_pi_right: coc.

Lemma star_lambda_left:
  forall t1 t2 b,
  [t1 =>* t2] -> [\t1, b =>* \t2, b].
Proof.
  induction 1; eauto with coc.
Defined.

Hint Resolve star_lambda_left: coc.

Lemma star_lambda_right:
  forall t b1 b2,
  [b1 =>* b2] -> [\t, b1 =>* \t, b2].
Proof.
  induction 1; eauto with coc.
Defined.

Hint Resolve star_lambda_right: coc.

Lemma star_application_left:
  forall f1 f2 x,
  [f1 =>* f2] -> [f1 @ x =>* f2 @ x].
Proof.
  induction 1; eauto with coc.
Defined.

Hint Resolve star_application_left: coc.

Lemma star_application_right:
  forall f x1 x2,
  [x1 =>* x2] -> [f @ x1 =>* f @ x2].
Proof.
  induction 1; eauto with coc.
Defined.

Hint Resolve star_application_right: coc.

Definition conv: pseudoterm -> pseudoterm -> Prop :=
  clos_refl_sym_trans _ step.

Hint Unfold conv: coc.
Hint Constructors clos_refl_sym_trans: coc.
Notation "[ a <=> b ]" := (conv a b): type_scope.

Lemma conv_beta:
  forall t b x,
  [(\t, b) @ x <=> b[x/]].
Proof.
  auto with coc.
Defined.

Lemma conv_step:
  forall a b, [a => b] -> [a <=> b].
Proof.
  auto with coc.
Defined.

Lemma conv_star:
  forall a b, [a =>* b] -> [a <=> b].
Proof.
  induction 1; eauto with coc.
Defined.

Lemma conv_refl:
  forall a, [a <=> a].
Proof.
  auto with coc.
Defined.

Lemma conv_tran:
  forall a b c, [a <=> b] -> [b <=> c] -> [a <=> c].
Proof.
  eauto with coc.
Defined.

Lemma conv_symm:
  forall a b, [a <=> b] -> [b <=> a].
Proof.
  auto with coc.
Defined.

Lemma subterm_and_step_commute:
  commut pseudoterm subterm step.
Proof.
  induction 1; eauto with coc.
Defined.

Inductive parallel: pseudoterm -> pseudoterm -> Prop :=
  | parallel_beta:
    forall t b1 b2 x1 x2,
    parallel b1 b2 -> parallel x1 x2 -> parallel ((\t, b1) @ x1) (b2[x2/])
  | parallel_type:
    parallel type type
  | parallel_prop:
    parallel prop prop
  | parallel_bound:
    forall n, parallel (bound n) (bound n)
  | parallel_pi:
    forall t1 t2 b1 b2,
    parallel t1 t2 -> parallel b1 b2 -> parallel (\/t1, b1) (\/t2, b2)
  | parallel_lambda:
    forall t1 t2 b1 b2,
    parallel t1 t2 -> parallel b1 b2 -> parallel (\t1, b1) (\t2, b2)
  | parallel_application:
    forall f1 f2 x1 x2,
    parallel f1 f2 -> parallel x1 x2 -> parallel (f1 @ x1) (f2 @ x2).

Hint Constructors parallel: coc.

Lemma parallel_refl:
  forall e, parallel e e.
Proof.
  simple induction e; auto with coc.
Defined.

Hint Resolve parallel_refl: coc.

Lemma parallel_step:
  forall a b, [a => b] -> parallel a b.
Proof.
  induction 1; auto with coc.
Defined.

Hint Resolve parallel_step: coc.

Lemma star_parallel:
  forall a b, parallel a b -> [a =>* b].
Proof.
  intros.
  induction H.
  - eapply star_tran.
    eapply star_tran.
    eapply star_application_left.
    apply star_lambda_right.
    eassumption.
    eapply star_application_right.
    eassumption.
    auto with coc.
  - auto with coc.
  - auto with coc.
  - auto with coc.
  - eauto with coc.
  - eauto with coc.
  - eauto with coc.
Defined.
