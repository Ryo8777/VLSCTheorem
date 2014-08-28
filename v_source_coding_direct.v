Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset bigop.
Require Import Reals Fourier.
Require Import Reals_ext log2 ssr_ext Rbigop proba entropy aep typ_seq natbin Rssr ceiling v_source_code.

Set Implicit Arguments.
Import Prenex Implicits.

Local Open Scope tuple_ext_scope.
Local Open Scope typ_seq_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.

Section Rsum_lemma.
Variable (X : finType) (n : nat).
Variable f : X -> R.
Hypothesis n_pos : (0 < n)%nat.
Variable S : {set  X}.

Lemma rsum_type_set :
  \rsum_(x in X) f(x) = \rsum_(x in [set : X]) f(x).
Proof.
by apply eq_bigl=>i; first rewrite in_setT.
Qed.

Lemma rsum_S_not_S:
  \rsum_(x| x \in [set : X]) f x =
  \rsum_(x| x \in S ) f x
                 + \rsum_(x| x \in ~: S) f x.
Proof. 
apply: rsum_union; first by rewrite disjoints_subset setCS.
by apply/setP=> ?; rewrite !inE orbN.
Qed.

Lemma log_pow k:
  log(INR (n ^ k)) = (INR k) * log (INR n).
Proof. 
elim: k => [| k IH].
  by rewrite mul0R expn0 log_1.
rewrite expnS -multE mult_INR log_mult; last first.
  apply lt_0_INR; apply/ltP; by rewrite expn_gt0 /orb n_pos.
  apply lt_0_INR; by apply/ltP.
by rewrite IH -addn1 plus_INR mulRDl addRC mul1R.
Qed.

End Rsum_lemma.

Section lemma_enc_dec.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : 0 < epsilon.

Lemma Xcard : 1 <= INR #|X|.
Proof.
rewrite (_ : 1 = INR 1) //.
apply le_INR. 
by apply /leP; first apply (dist_support_not_empty P).
Qed.

Definition L0 := ceil (INR n * (`H P + epsilon)).

Lemma L0_pos: 0 < IZR L0.
Proof.
rewrite /L0.
apply (Rlt_le_trans _ (INR n * (`H P + epsilon))); last by apply ceil_bottom.
rewrite -(mulR0 0).
apply (Rmult_le_0_lt_compat _ _ _ _ (Rle_refl _) (Rle_refl _)).
apply lt_0_INR; by apply/ltP.
by apply (Rplus_le_lt_0_compat _ _ (entropy_pos P) ep_pos).
Qed.

Definition L1 :=  ceil (log (INR #| [set : n.-tuple X]|)).
  
Lemma L1_nonneg: 0 <= IZR L1.
Proof.
apply (Rle_trans _ (log (INR #|[set: n.-tuple X]|))); last by apply ceil_bottom.
rewrite -log_1.
apply (log_increasing_le Rlt_0_1).
rewrite cardsT card_tuple -INR_pow_expn.
by apply pow_R1_Rle, Xcard. 
Qed.

Lemma IZR_INR_to_nat z: 0 <= IZR z -> IZR z = INR (Zabs_nat z).
Proof.
move => H.
rewrite -INR_Zabs_nat ;last by apply le_IZR.
by rewrite Zabs2Nat.abs_nat_nonneg //; first apply le_IZR.
Qed.

Lemma card_TS_le_L0 : INR #| `TS P n epsilon | <= INR #|[ set : (Zabs_nat L0).-tuple bool]|. 
Proof.
apply (Rle_trans _ _ _ (TS_sup _ _ _)).
rewrite cardsT /= card_tuple /= card_bool -exp2_pow2.
apply exp2_le_increasing.
rewrite -IZR_INR_to_nat; last apply RltW, L0_pos.
by apply ceil_bottom. 
Qed.

Lemma card_tuple_le_L1 : INR #| [set: n.-tuple X]| <= INR #| [set: (Zabs_nat L1).-tuple bool]|.
Proof.
rewrite /L1 cardsT card_tuple.
rewrite {1}(_ :  INR (#|X| ^ n) = exp2 (log ( INR (#|X|^n)))); last first.
  rewrite exp2_log //; last rewrite -INR_pow_expn.
  apply pow_lt.
  apply (Rlt_le_trans _ 1 _ Rlt_0_1 Xcard).
rewrite cardsT card_tuple card_bool -exp2_pow2.
apply exp2_le_increasing.
rewrite /L1 -IZR_INR_to_nat; last first.
  apply (Rle_trans _ (log (INR (#|X|^n)))); last by apply ceil_bottom.  
  rewrite -log_1. 
  apply log_increasing_le; first by apply Rlt_0_1.
  rewrite -INR_pow_expn.
  by apply pow_R1_Rle, Xcard. 
by apply (Rle_trans _ _ _ (Rle_refl _) (ceil_bottom _)).
Qed.

End lemma_enc_dec.

Section enc_dec_def.
Local Open Scope nat_scope.

Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : (0 < epsilon)%R.

Local Notation "'L0'" := (L0 n' P epsilon).
Local Notation "'L1'" := (L1 X n').

Lemma le_n_L1_tuple :
  #|[finType of n.-tuple X] | <= #|[finType of (Zabs_nat L1).-tuple bool]|.
Proof.
rewrite -!cardsT.
by apply /leP; apply (INR_le _ _ (card_tuple_le_L1 n' P)).
Qed.

Definition not_enc_typ x := enum_val (widen_ord le_n_L1_tuple (enum_rank x)).

Lemma inj_not_enc_typ : injective not_enc_typ.
Proof.
by move=> a1 a2 [] /enum_val_inj [] /ord_inj/enum_rank_inj.
Qed.

Definition enc_typ x :=
 let i := seq.index x (enum (`TS P n epsilon))
 in Tuple (size_nat2bin i (Zabs_nat L0)).

(* Definition enc_typ x := *)
(*  let i := seq.index x (enum (`TS P n epsilon)) *)
(*  in nat2bin i (Zabs_nat L0). *)

Definition f : var_enc X n := fun x =>
  if x \in `TS P n epsilon then
    true :: enc_typ x
  else 
    false :: not_enc_typ x.

Lemma f_inj : injective f.
Proof.
move=> t1 t2.
rewrite /f.
case/boolP : (t1 == t2); first by move=> /eqP.
move=> t1t2.
case: ifP => Ht1.
  case: ifP => Ht2 //.
  case => H.
  have {H}H : seq.index t1 (enum (`TS P n epsilon)) =
              seq.index t2 (enum (`TS P n epsilon)).
    apply (nat2bin_inj (Zabs_nat L0)) => //.
    apply leq_trans with #|`TS P n epsilon|.
      apply seq_index_enum_card => //; first by exact: enum_uniq.
      apply/leP.
      apply INR_le.
      move: (card_TS_le_L0 n' P ep_pos).
      by rewrite {1}cardsT card_tuple /= card_bool.
    apply leq_trans with #|`TS P n epsilon|.
      apply seq_index_enum_card => //; first by exact: enum_uniq.
      apply/leP.
      apply INR_le.
      move: (card_TS_le_L0 n' P ep_pos).
      by rewrite {1}cardsT card_tuple /= card_bool.
  rewrite -(@nth_index _ t1 t1 (enum (`TS P n epsilon))); last by rewrite mem_enum.
  rewrite -(@nth_index _ t1 t2 (enum (`TS P n epsilon))); last by rewrite mem_enum.
  by rewrite H.
case: ifP => Ht2 //.
case => H.
apply (inj_not_enc_typ t1 t2).
by apply val_inj.
Qed.

Definition phi_def : n.-tuple X.
move: (dist_support_not_empty P) => H.
move Hpick : [pick x | x \in [set: X] ] => p.
move: Hpick.
case: (pickP _).
  move=> x _ _.
  exact [tuple of nseq n x].
move=> abs H'.
suff : False by done.
move: H.
rewrite -cardsT card_gt0.
case/set0Pn => ?.
by rewrite abs.
Defined.

Definition phi y := if [ pick x | f x == y ] is Some x then x else phi_def.

Lemma phi_f x : phi (f x) = x.
Proof.
rewrite /phi.
case: (pickP _) => [x0 /eqP | H].
  by apply f_inj.
move: (H x).
by rewrite eqxx.
Qed.

Definition extension (enc : var_enc X n) (x : seq (n.-tuple X)) :=
flatten (map enc x).

Lemma uniquely_decodable : injective (extension f).
Proof.
move =>t1.
elim t1=>[t2|a la H t2].
by case t2=>[|a la] //; rewrite /extension /f /=; case: ifP.
case t2=>[|b lb]; [by rewrite /extension /f /=; case: ifP | rewrite /extension /= /f ].
case: ifP=> [ainT | aninT].
  case: ifP=> binT //.
  move /eqP.
  rewrite  -/f eqseq_cat; last by rewrite /= !/nat2bin !size_pad_seqL.
  case /andP=>[/eqP eq_ab ] /eqP /H ->.
  congr (_ :: _); by apply f_inj; rewrite /f ainT binT.
case: ifP=> bninT //.
move /eqP.
rewrite  -/f eqseq_cat; last by rewrite !size_tuple. 
case /andP=>[/eqP eq_ab ] /eqP /H ->.
congr (_ :: _); by apply f_inj; rewrite /f aninT bninT.
Qed. 

End enc_dec_def.

Section exp_len_cw_def.
Variable (X : finType) (n :nat).
Variable f : var_enc X n.
Variable P : dist X.

Definition exp_len_cw := `E (mkRvar (P `^ n) (fun x => INR (size (f x)))).

End exp_len_cw_def.

Section main_pre.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon:R.
Hypothesis ep_pos: 0 < epsilon.
Hypothesis aepbound : aep_bound P epsilon <= INR n.

Local Notation "'L0'" := (L0 n' P epsilon).
Local Notation "'L1'" := (L1 X n').

Lemma fdef_in x : x \in `TS P n epsilon -> INR (size (f P epsilon x)) = (IZR L0) + 1.
Proof.
move => H.
rewrite /f H /= size_pad_seqL IZR_INR_to_nat; last by apply RltW, L0_pos.
by rewrite -addn1; first rewrite plus_INR.
Qed.

Lemma fdef_notin x : x \in ~: `TS P n epsilon -> INR (size (f P epsilon x)) = (IZR L1) + 1.
Proof.
rewrite /f in_setC.
move/negbTE ->.
rewrite /= -addn1 size_tuple plus_INR.
by rewrite -IZR_INR_to_nat; last apply L1_nonneg.
Qed.

Lemma Hexp_len_cw : 
  exp_len_cw (f (n':=n') P epsilon) P 
  = \rsum_(x in [finType of n.-tuple X])( P`^n(x) * (INR (size (f P epsilon x)))).
Proof.
apply eq_bigr => /= x _.
by rewrite mulRC.
Qed.

Lemma f_typ_in :  
  \rsum_(x| x \in `TS P n epsilon) P `^ n (x) * (INR (size (f P epsilon x)) ) =  
  \rsum_(x| x \in `TS P n epsilon) P `^ n (x) * (IZR L0 + 1).
Proof.
apply eq_bigr=> i H.
apply Rmult_eq_compat_l.
by apply fdef_in.
Qed.

Lemma f_typ_notin:
  \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (INR (size (f P epsilon x)) )
  = \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (IZR L1 + 1) .
Proof.
apply eq_bigr=> i H.
apply Rmult_eq_compat_l.
by apply fdef_notin.
Qed.

Lemma theorem_helper : \rsum_(x| x \in (`TS P n epsilon)) P `^ n (x) * (IZR L0 + 1)
                       +  \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (IZR L1 + 1) 
                       <=  (IZR L0 + 1) + epsilon * (IZR L1 + 1) .
Proof.
rewrite -!(big_morph _ (morph_mulRDl _) (mul0R _)) mulRC.
rewrite (_ : \rsum_(i | i \in ~: `TS P n epsilon) P `^ n i = 1 - \rsum_(i | i \in `TS P n epsilon) P `^ n i); last first. 
  rewrite -(pmf1 P`^n) rsum_type_set (rsum_S_not_S _ (`TS P n epsilon)) ; field.
apply Rplus_le_compat.
  rewrite -[X in _ <= X]mulR1.
  apply Rmult_le_compat_l. 
    apply Rplus_le_le_0_compat; by [apply RltW, L0_pos| apply Rle_0_1].
  rewrite -(pmf1 P`^ n). 
  apply Rle_big_f_X_Y=> //; first move=> ?; apply pmf.
apply Rmult_le_compat_r.
  by apply (Rplus_le_le_0_compat _ _ (L1_nonneg _ P) Rle_0_1).
apply Rminus_le.
rewrite /Rminus addRC addRA.
apply Rle_minus.
rewrite addRC.
by apply Rge_le; apply Pr_TS_1.
Qed.

End main_pre.

Section main.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : 0 < epsilon .
Definition epsilon':= epsilon / (3 + (3 * log (INR #|X|))).
Definition n0 := maxn (Zabs_nat (ceil (INR 2 / (INR 1 + log (INR #|X|))))) 
                     (maxn (Zabs_nat (ceil (8 / epsilon)))
                     (Zabs_nat (ceil (aep_sigma2 P/ epsilon' ^ 3)))).
Hypothesis n0_n : (n0 < n)%coq_nat.

Lemma n1_le_n : (Zabs_nat (ceil (INR 2 / (INR 1 + log (INR #|X|)))) < n)%coq_nat.
Proof.
move/ltP : n0_n.
rewrite /n0 gtn_max.
by case/andP => /ltP.
Qed.

Lemma n2_le_n : (Zabs_nat (ceil (8 / epsilon)) < n)%coq_nat.
Proof.
move/ltP : n0_n.
do 2 rewrite /n0 gtn_max.
case/andP=> H. 
case/andP=> H1 H2.
by apply /ltP.
Qed.

Lemma n3_le_n : (Zabs_nat (ceil (aep_sigma2 P / epsilon' ^ 3 )) < n)%coq_nat.
Proof.
move/ltP : n0_n.
do 2 rewrite /n0 gtn_max.
case/andP=> H. 
case/andP=> H1 H2.
by apply /ltP.
Qed.

Lemma n_non0 : INR n <> 0.
Proof.
apply nesym, Rlt_not_eq.
by apply lt_0_INR; apply/ltP.
Qed.

Lemma n0_n_helper1: 1 + log (INR #|X|) <> 0.
Proof.
apply nesym, Rlt_not_eq, Rplus_lt_le_0_compat; first by apply Rlt_0_1.
rewrite -log_1.
apply log_increasing_le; first by apply Rlt_0_1.
by apply Xcard.
Qed.

Lemma n0_n_helper2 : INR n <> 0 /\ 1 + log (INR #|X|) <> 0.
Proof.
split.
apply n_non0.
apply n0_n_helper1.
Qed. 

Lemma n0_n_1 :  2 * (epsilon / (3 * (1 + log (INR #|X|)))) / INR n < epsilon / 3.
Proof.
rewrite (_ : 2 * _ / _ = epsilon * (2 /  (3 * (1 + log (INR #|X|))) / INR n)); last first.
  field; by case: n0_n_helper2.
apply Rmult_lt_compat_l; first by apply ep_pos.
apply (Rmult_lt_reg_l 3); first by fourier.
rewrite (_ : 3 * _ = 2 * 3 / 3 / (1 + log (INR #|X|)) * / INR n); last first.
  field; by case: n0_n_helper2.
rewrite /Rdiv Rinv_r_simpl_l; last by move=> ?; fourier.
apply (Rmult_lt_reg_l (INR n)); first by apply lt_0_INR; apply/ltP.
rewrite (_ : _ * _ = (2 * / (1 + log (INR #|X|)) * INR n  * / INR n)); last first.
  field; by case: n0_n_helper2.
rewrite (Rinv_r_simpl_l _ _ n_non0).
apply (Rle_lt_trans _ _ _ (ceil_bottom _)).
rewrite IZR_INR_to_nat; last first.
  apply (Rle_trans _ (2 * / (1 + log (INR #|X|)))); last by apply ceil_bottom.
  apply (Rmult_le_reg_l (1 + log (INR #|X|))); last first.
    rewrite (_ : _ * (_ * / _) = 
                 2 * (1 + log (INR #|X|)) * / (1 + log (INR #|X|))); last first.
      field; exact n0_n_helper1.
    rewrite (Rinv_r_simpl_l _ _ n0_n_helper1).
    rewrite mulR0; fourier.
  apply (Rplus_lt_le_0_compat _ _ Rlt_0_1).
  rewrite -log_1.
  apply log_increasing_le; first by fourier.
  apply (Xcard P).
rewrite Rinv_r; last by move=> ?; fourier.
rewrite mulR1.
apply (lt_INR _ _ n1_le_n).
Qed.

Lemma n0_n_2 :  2 * / INR n  < epsilon / 4.
Proof.
apply (Rmult_lt_reg_l 4); first fourier.
rewrite /Rdiv (mulRC epsilon (/ 4)) mulRA mulRA Rinv_r ; last by move => ? ; fourier.
apply (Rmult_lt_reg_l (INR n)); first by apply lt_0_INR; apply /ltP. 
rewrite (_ : _ * (_ * _ * / _) = 8 * INR n * / INR n); last by field; exact n_non0.
rewrite (Rinv_r_simpl_l _ _ n_non0).
apply (Rmult_lt_reg_l ( / epsilon)).
  apply (Rmult_lt_reg_l epsilon _ _ ep_pos).
  rewrite Rinv_r; first by rewrite mulR0; apply Rlt_0_1.
  by apply nesym, Rlt_not_eq, ep_pos.
rewrite mul1R (mulRC (/ epsilon) (INR n * epsilon)).
rewrite Rinv_r_simpl_l; last by apply nesym, Rlt_not_eq, ep_pos.
rewrite mulRC.
apply (Rle_lt_trans _ (IZR (ceil (8 * / epsilon))) _ (ceil_bottom _)).
rewrite IZR_INR_to_nat; first by apply lt_INR, n2_le_n.
eapply Rle_trans;  last by apply ceil_bottom.
apply (Rmult_le_reg_l epsilon _ _ ep_pos).
rewrite (mulRC 8  (/ epsilon)) mulRA Rinv_r; last by apply nesym, Rlt_not_eq, ep_pos.
rewrite mulR0; fourier.
Qed.

Lemma ep'_pos : 0 < epsilon'.
Proof. 
rewrite /epsilon' /Rdiv. 
rewrite -(mulR0 epsilon).
apply (Rmult_lt_compat_l _ _ _ ep_pos).
rewrite -(mul1R ( / (3 + 3 * log (INR #|X|)))).
apply (Rlt_mult_inv_pos _ _ Rlt_0_1).
apply Rplus_lt_le_0_compat; first by apply Rlt_zero_pos_plus1, Rlt_R0_R2.
apply Rmult_le_pos; first by apply Rle_zero_pos_plus1, Rle_zero_pos_plus1, Rle_0_1.
rewrite -log_1.
by apply (log_increasing_le Rlt_0_1 (Xcard P)).
Qed.


Lemma n0_n_3 : aep_bound P epsilon' <= INR n.
Proof.
rewrite /aep_bound .
eapply (Rle_trans _ _ _ (ceil_bottom _)).
rewrite IZR_INR_to_nat; last first.
  apply (Rle_trans _ (aep_sigma2 P / epsilon' ^ 3)); last by apply (ceil_bottom _).
  apply (Rmult_le_reg_l ( epsilon' ^ 3) _ _ (pow_gt0 ep'_pos 3)).
  rewrite (_ : _ * ( _ / _) = aep_sigma2 P * epsilon' ^ 3  * / (epsilon' ^ 3)); last first.
    by field; apply nesym, Rlt_not_eq, ep'_pos.
  rewrite Rinv_r_simpl_l; last by apply nesym, Rlt_not_eq, pow_gt0, ep'_pos.
  rewrite mulR0.
  by apply aep_sigma2_pos.
by apply RltW, lt_INR, n3_le_n.
Qed. 

Lemma v_scode_helper : exists (f : var_enc X n) (phi : var_dec X n) , 
                         (forall x, phi (f x) = x) /\
                         (exp_len_cw f P) / (INR n) < (`H P + epsilon).
Proof.
exists (f P epsilon') .
exists (phi n' P epsilon').
split=> [ x |]; first  by apply (phi_f _ ep'_pos).
apply (Rmult_lt_reg_r (INR n)); first by apply lt_0_INR; apply /ltP.
rewrite /Rdiv -mulRA -(mulRC (INR n)).
rewrite (Rinv_r _ n_non0).
rewrite mulR1 Hexp_len_cw rsum_type_set (rsum_S_not_S _ (`TS P n epsilon')).
rewrite f_typ_notin f_typ_in; last apply ep'_pos.
eapply Rle_lt_trans.
  apply (theorem_helper _  ep'_pos).
  by apply n0_n_3.
rewrite /L0 /L1.
eapply Rle_lt_trans.
  apply Rplus_le_compat.
    by apply Rplus_le_compat; by [apply RltW, ceil_upper | apply Rle_refl].
  apply Rmult_le_compat_l; first by apply Rlt_le, ep'_pos.
  by apply Rplus_le_compat; by [apply RltW, ceil_upper | apply Rle_refl].
rewrite cardsT card_tuple.
rewrite log_pow; last by apply (dist_support_not_empty P).
rewrite (_ : _ * _ + _ + _ + _ *( _ * _ + _ + _) =
             INR n * (`H P + epsilon') + 2 +
             epsilon' * (INR n * log (INR #|X|) + 2)); last first.
  rewrite /n.
  by field.
rewrite  -(Rinv_r_simpl_l (INR n) 2); last by apply n_non0.
rewrite (_ :  _ * _ + _ * _ / _ =
              INR n * (`H P + epsilon' + 2 / INR n)) ;last first. 
  field; by apply n_non0.
rewrite (_ :  _ * _ * / _ = INR n * (2  / INR n)); last first.
  field; by apply n_non0.
rewrite (_ :  INR n * _ + INR n * _ = 
                (INR n * (log (INR #|X|) + (2 / INR n)))); last first.
  field; by apply n_non0.
rewrite (_ :   _ * _ + _ * _ =
               INR n * (`H P + epsilon' + 2 / INR n +  epsilon' * (log (INR #|X|) + 2 / INR n))); last first.
  field; by apply n_non0.
rewrite mulRC.
apply Rmult_lt_compat_r.
  by apply lt_0_INR; apply /ltP.
do 2 rewrite -addRA.
apply Rplus_lt_compat_l.
rewrite (_ : epsilon' * _ =
               epsilon' * (log (INR #|X|)) + epsilon' * 2 / INR n); last first.
  field; by apply n_non0.
rewrite (_ :   _ + (_ / _ + _) =
               2 / INR n +
               epsilon' * (1 + log (INR #|X|)) + epsilon' * 2 / INR n) ; last first.
  field; by apply n_non0.
rewrite (_ : _ * _ / _ = 2 * epsilon' / INR n); last first.
  field; by apply n_non0.
rewrite /epsilon'.
rewrite (_ : (3 + 3 * _ = 3 * (1 + log (INR #|X|)))); last field.
rewrite {1}(_ : epsilon / _ = 
                epsilon / 3 / (1 + log (INR #|X|) )); last first.
  field; by apply n0_n_helper1.
rewrite (_ : _ / _ / _ * _ =
             epsilon  * (1 + log (INR #|X|))/ (1 + log (INR #|X|)) /3); last first.
  field; by apply n0_n_helper1.
rewrite /Rdiv (Rinv_r_simpl_l _ _ n0_n_helper1).
eapply Rle_lt_trans.
  apply Rplus_le_compat; last by apply RltW, n0_n_1.
    by apply Rplus_le_compat; by [apply RltW, n0_n_2 | apply Rle_refl].
rewrite (_ : _ / _ + _ / _ + _ / _ = epsilon * ( / 4 + / 3 + / 3)) ; last field.
rewrite -{2}(mulR1 epsilon).
apply (Rmult_lt_compat_l _ _ _ ep_pos).
fourier.
Qed.

End main.

Section variable_length_source_coding.

Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : 0 < epsilon .
(*Definition n0 := maxn 
          (Z.to_nat (ceil (INR 2 / (INR 1 + log (INR #|X|))))) 
          (maxn (Z.to_nat (ceil (8 / epsilon)))
          (Z.to_nat (ceil (aep_sigma2 P/ epsilon' ^ 3)))).*)
Local Notation "'n0'" := (n0 P epsilon).


Theorem vscode : (n0 < n)%nat -> 
  exists f : var_enc X n,
    injective f /\
    exp_len_cw f P / INR n < `H P + epsilon.
Proof.
move/ltP.
case/v_scode_helper => // f [phi [fphi ccl]].
exists f.
split => //.
by apply can_inj with phi.
Qed.

End variable_length_source_coding.
