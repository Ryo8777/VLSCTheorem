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

Section set_lemma.
Variable X : finType.
Variable S: {set X}.

Lemma set_complement:
  [set :  X] = S :|: ~:S.
Proof.
by apply/setP => x; rewrite !inE orbN. 
Qed.

Lemma disjoint_set_complement:
  [disjoint S & ~: S].
Proof.
by rewrite disjoints_subset subsetC setCS.
Qed.

End set_lemma.

Section Rsum_lemma.
Variable (X : finType) (n : nat).
Variable f : X -> R.
Hypothesis n_pos : (0 < n)%nat.
Variable S : {set  X}.

Lemma rsum_type_set :
  \rsum_(x in X) f(x) = \rsum_(x in [set : X]) f(x).
Proof.
elim: (index_enum X) => [| hd tl IH].
- by rewrite !big_nil.
- rewrite !big_cons. 
  rewrite in_setT. 
  by rewrite /= IH.
Qed.

Lemma rsum_fr_rf r U:
  \rsum_(x | U x) (f(x) * r) = r * \rsum_(x | U x) f(x) .
Proof.
elim: (index_enum X) => [| hd tl IH].
- by rewrite !big_nil mulR0.
- rewrite !big_cons IH mulRC.
  case (U hd); [ by rewrite mulRDr | by []].
Qed.

Lemma rsum_S_not_S:
  \rsum_(x| x \in [set : X]) f x =
  \rsum_(x| x \in S ) f x
                 + \rsum_(x| x \in ~: S) f x.
Proof. 
apply rsum_union.
  by rewrite disjoint_sym; by apply disjoint_set_complement.
by apply set_complement. 
Qed.

Lemma log_pow k:
  log(INR (n ^ k)) = (INR k) * log (INR n ).
Proof. 
elim: k => [| k IH].
  by rewrite mul0R expn0 log_1.
rewrite expnS -multE mult_INR log_mult; last 2 first.
  apply lt_0_INR; by apply/ltP.
  apply lt_0_INR; apply/ltP; by rewrite expn_gt0 /orb n_pos.
by rewrite IH -addn1 plus_INR mulRDl addRC mul1R.
Qed.

End Rsum_lemma.

Section Rsum_probability.
Variable X : finType.
Variable S : {set  X}.
Variable P : dist X.

Lemma rsum_complement_dist :  \rsum_(x| x \in ~:S) P x
               =  (1- \rsum_(x| x \in S) P x).
Proof.
by rewrite -(pmf1 P) rsum_type_set (rsum_S_not_S _ S); field.
Qed.

End Rsum_probability.

Section lemma_enc_dec.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : 0 < epsilon.

Lemma Xcard : 1 <= INR #|X|.
Proof.
rewrite (_ : 1 = INR 1) //.
apply le_INR; apply /leP.
by apply dist_support_not_empty, P.
Qed.

Definition L_0 := ceil (INR n * (`H P + epsilon)).

Lemma L_0_pos: 0 < IZR L_0.
Proof.
rewrite /L_0.
apply Rlt_le_trans with (INR n * (`H P + epsilon)).
  rewrite -(mulR0 0).
  apply Rmult_le_0_lt_compat; first by apply Rle_refl.
  by apply Rle_refl.
  apply lt_0_INR; by apply/ltP.
  by apply Rplus_le_lt_0_compat; first apply entropy_pos; last apply ep_pos.
by apply ceil_bottom.
Qed.

Definition L_1 :=  ceil (log (INR #| [set : n.-tuple X]|)).
  
Lemma L_1_nonneg: 0 <= IZR L_1.
Proof.
apply Rle_trans with (log (INR #|[set: n.-tuple X]|)); last by apply ceil_bottom.
rewrite -log_1.
apply log_increasing_le; first by apply Rlt_0_1.
rewrite cardsT card_tuple -INR_pow_expn.
by apply pow_R1_Rle, Xcard. 
Qed.

Lemma IZR_INR_to_nat z: 0 <= IZR z -> IZR z = INR (Zabs_nat z).
Proof.
move => H.
rewrite -INR_Zabs_nat ;last by apply le_IZR.
by rewrite Zabs2Nat.abs_nat_nonneg; [ done | apply le_IZR].
Qed.

Lemma card_TS_le_L0 : INR #| `TS P n epsilon | <= INR #|[ set : (Zabs_nat L_0).-tuple bool]|. 
Proof.
eapply Rle_trans; first by apply TS_sup.
rewrite cardsT /= card_tuple /= card_bool -exp2_pow2.
apply exp2_le_increasing.
rewrite -IZR_INR_to_nat; last apply RltW, L_0_pos.
by apply ceil_bottom. 
Qed.

Lemma card_tuple_le_L1 : INR #| [set: n.-tuple X]| <= INR #| [set: (Zabs_nat L_1).-tuple bool]|.
Proof.
rewrite /L_1 cardsT card_tuple.
rewrite {1}(_ :  INR (#|X| ^ n) = exp2 (log ( INR (#|X|^n)))); last first.
  rewrite exp2_log; first done; last rewrite -INR_pow_expn.
  apply pow_lt, Rlt_le_trans with 1; by [apply Rlt_0_1 | apply Xcard].
rewrite cardsT card_tuple card_bool -exp2_pow2.
apply exp2_le_increasing.
rewrite /L_1 -IZR_INR_to_nat; last first.
  apply Rle_trans with (log (INR (#|X|^n))); last by apply ceil_bottom.  
  rewrite -log_1. 
  apply log_increasing_le; first by apply Rlt_0_1.
  rewrite -INR_pow_expn.
  by apply pow_R1_Rle, Xcard. 
by eapply Rle_trans ; [ apply Rle_refl | apply ceil_bottom].
Qed.

End lemma_enc_dec.

Section enc_dec_def.
Local Open Scope nat_scope.

Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : (0 < epsilon)%R.

Local Notation "'L_0'" := (L_0 n' P epsilon).
Local Notation "'L_1'" := (L_1 X n').

Lemma le_n_L1_tuple :
  #|[finType of n.-tuple X] | <= #|[finType of (Zabs_nat L_1).-tuple bool]|.
Proof.
apply /leP.
do 2 rewrite -cardsT.
move : (card_tuple_le_L1 n' P).
by apply INR_le.
Qed.

Definition not_enc_typ x := enum_val (widen_ord le_n_L1_tuple (enum_rank x)).

Lemma inj_not_enc_typ : injective not_enc_typ.
Proof.
by move=> a1 a2 [] /enum_val_inj [] /ord_inj/enum_rank_inj.
Qed.

Definition enc_typ x :=
 let i := seq.index x (enum (`TS P n epsilon))
 in Tuple (size_nat2bin i (Zabs_nat L_0)).

Definition f : v_encT X n := fun x =>
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
    apply nat2bin_inj with (Zabs_nat L_0) => //.
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
rewrite -cardsT in H.
rewrite card_gt0 in H.
case/set0Pn : H => x Hx.
by rewrite abs in Hx.
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

Definition extension (enc : v_encT X n) (x : seq (n.-tuple X)) :=
flatten (map enc x).

Lemma uniquely_decodable : injective (extension f).
Proof.
move =>t1.
elim t1=>[t2|a la H t2].
by case t2=>[|a la];[done | rewrite /extension /f /=; case: ifP].
case t2=>[|b lb]; [by rewrite /extension /f /=; case: ifP | rewrite /extension /= /f ].
case: ifP=> [ainT | aninT].
  case: ifP=> binT; last done.
  move /eqP.
  rewrite  -/f eqseq_cat; last by rewrite /= !/nat2bin !size_pad_seqL.
  case /andP=>[/eqP eq_ab ] /eqP /H ->.
  congr (_ :: _); by apply f_inj; rewrite /f ainT binT.
case: ifP=> bninT; first done.
move /eqP.
rewrite  -/f eqseq_cat; last by rewrite !size_tuple. 
case /andP=>[/eqP eq_ab ] /eqP /H ->.
congr (_ :: _); by apply f_inj; rewrite /f aninT bninT.
Qed. 

End enc_dec_def.

Section exp_len_cw_def.
Variable (X : finType) (n :nat).
Variable f : v_encT X n.
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

Local Notation "'L_0'" := (L_0 n' P epsilon).
Local Notation "'L_1'" := (L_1 X n').

Lemma fdef_in x : x \in `TS P n epsilon -> INR (size (f P epsilon x)) = (IZR L_0) + 1.
Proof.
move => H.
rewrite /f H /= size_pad_seqL IZR_INR_to_nat; last by apply RltW, L_0_pos.
by rewrite -addn1; first rewrite plus_INR.
Qed.

Lemma fdef_notin x : x \in ~: `TS P n epsilon -> INR (size (f P epsilon x)) = (IZR L_1) + 1.
Proof.
rewrite /f in_setC => H.
apply negbTE in H.
rewrite H /= -addn1 size_tuple plus_INR.
by rewrite -IZR_INR_to_nat ; last apply L_1_nonneg.
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
  \rsum_(x| x \in `TS P n epsilon) P `^ n (x) * (IZR L_0 + 1).
Proof.
elim: (index_enum [finType of n.-tuple X]) => [| hd tl IH].
- by rewrite !big_nil.
- rewrite !big_cons. 
  case : ifP => H; last done.
  by rewrite fdef_in; [rewrite IH | done]. 
Qed.

Lemma f_typ_notin:
  \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (INR (size (f P epsilon x)) )
  = \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (IZR L_1 + 1) .
Proof.
elim: (index_enum [finType of n.-tuple X]) => [| hd tl IH].
- by rewrite !big_nil.
- rewrite !big_cons. 
  case : ifP => H; last done.
  by rewrite fdef_notin; [rewrite IH | done]. 
Qed.

Lemma theorem_helper : \rsum_(x| x \in (`TS P n epsilon)) P `^ n (x) * (IZR L_0 + 1)
                       +  \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (IZR L_1 + 1) 
                       <=  (IZR L_0 + 1) + epsilon * (IZR L_1 + 1) .
Proof.
do 2 rewrite rsum_fr_rf.
rewrite rsum_complement_dist.
apply Rplus_le_compat.
  rewrite {2}(_ : _ + _  =  (IZR L_0 + 1) * 1); last field. 
  apply Rmult_le_compat_l; first apply Rplus_le_le_0_compat; first by apply RltW,L_0_pos.
    by apply Rle_0_1.
  rewrite -(pmf1 P`^ n). 
  apply Rle_big_f_X_Y; first move=> x; last by move=> x H.
  by apply pmf.
rewrite mulRC.
apply Rmult_le_compat_r.
  by apply Rplus_le_le_0_compat; [apply L_1_nonneg| fourier].
apply Rminus_le.
rewrite (_ : _ - _ - _ = 1 - epsilon - \rsum_(x|x \in `TS P n epsilon) P `^ n x)
; last first.
  rewrite /=.
  field.
by apply Rle_minus, Rge_le, Pr_TS_1; by [apply ep_pos | apply aepbound].
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
apply Rmult_lt_reg_l with 3; first by fourier.
rewrite (_ : 3 * _ = 2 * 3 / 3 / (1 + log (INR #|X|)) * / INR n); last first.
  field; by case: n0_n_helper2.
rewrite /Rdiv Rinv_r_simpl_l; last first.
  move=> ?; fourier.
apply Rmult_lt_reg_l with (INR n). 
  apply lt_0_INR; by apply/ltP.
rewrite (_ : _ * _ = (2 * / (1 + log (INR #|X|)) * INR n  * / INR n)); last first.
  field; by case: n0_n_helper2.
rewrite Rinv_r_simpl_l; last by apply n_non0.
eapply Rle_lt_trans; first by apply ceil_bottom.
rewrite IZR_INR_to_nat; last first.
  eapply Rle_trans; last by apply ceil_bottom.
  apply Rmult_le_reg_l with (1 + log (INR #|X|)); last first.
    rewrite (_ : _ * (_ * / _) = 
                 2 * (1 + log (INR #|X|)) * / (1 + log (INR #|X|))); last first.
      field; exact n0_n_helper1.
    rewrite Rinv_r_simpl_l; last by exact n0_n_helper1.
    rewrite mulR0; fourier.
  apply Rplus_lt_le_0_compat; first by apply Rlt_0_1.
  rewrite -log_1.
  apply log_increasing_le; first by fourier.
  apply Xcard; exact P.
rewrite Rinv_r; last by move=> ?; fourier.
rewrite mulR1.
apply lt_INR.
exact n1_le_n.
Qed.

Lemma n0_n_2 :  2 * / INR n  < epsilon / 4.
Proof.
apply Rmult_lt_reg_l with 4; first fourier.
rewrite /Rdiv (mulRC epsilon (/ 4)) mulRA mulRA Rinv_r ; last first.
  move => ? ; fourier.
apply Rmult_lt_reg_l with (INR n).
  by apply lt_0_INR; apply /ltP. 
rewrite (_ : _ * (_ * _ * / _) = 8 * INR n * / INR n); last first.
  field; exact n_non0.
rewrite Rinv_r_simpl_l; last by exact n_non0.
apply Rmult_lt_reg_l with ( / epsilon).
  apply Rmult_lt_reg_l with epsilon ; first by apply  ep_pos.
  rewrite Rinv_r.
    by rewrite mulR0; apply Rlt_0_1.
  by apply nesym, Rlt_not_eq, ep_pos.
rewrite mul1R (mulRC (/ epsilon) (INR n * epsilon)).
rewrite Rinv_r_simpl_l; last first.
  by apply nesym, Rlt_not_eq, ep_pos.
rewrite mulRC.
apply Rle_lt_trans with (IZR (ceil (8 * / epsilon))).
  by apply ceil_bottom.
rewrite IZR_INR_to_nat; first by apply lt_INR, n2_le_n.
eapply Rle_trans;  last first.
  apply ceil_bottom.
apply Rmult_le_reg_l with epsilon; first exact ep_pos.
rewrite (mulRC 8  (/ epsilon)) mulRA Rinv_r; last first.
 by apply nesym, Rlt_not_eq, ep_pos.
rewrite mulR0; fourier.
Qed.

Lemma ep'_pos : 0 < epsilon'.
Proof. 
rewrite /epsilon' /Rdiv. 
rewrite -(mulR0 epsilon).
apply Rmult_lt_compat_l; first by apply ep_pos.
rewrite -(mul1R ( / (3 + 3 * log (INR #|X|)))).
apply Rlt_mult_inv_pos; first by apply Rlt_0_1.
apply Rplus_lt_le_0_compat; first by apply Rlt_zero_pos_plus1, Rlt_R0_R2.
apply Rmult_le_pos; first by apply Rle_zero_pos_plus1, Rle_zero_pos_plus1, Rle_0_1.
rewrite -log_1.
by apply log_increasing_le; [apply Rlt_0_1 | apply Xcard].
Qed.

Lemma n0_n_3 : aep_bound P epsilon' <= INR n.
Proof.
rewrite /aep_bound .
eapply Rle_trans.
  by apply ceil_bottom.
rewrite IZR_INR_to_nat; last first.
  eapply Rle_trans; last first.
    by apply ceil_bottom.
  apply Rmult_le_reg_l with ( epsilon' ^ 3). 
    by apply pow_gt0; first by apply ep'_pos.
  rewrite (_ : _ * ( _ / _) = aep_sigma2 P * epsilon' ^ 3  * / (epsilon' ^ 3)); last first.
    by field; apply nesym, Rlt_not_eq, ep'_pos.
  rewrite Rinv_r_simpl_l; last first.
    by apply nesym, Rlt_not_eq, pow_gt0, ep'_pos.
  rewrite mulR0.
  by apply aep_sigma2_pos.
by apply RltW, lt_INR, n3_le_n.
Qed. 

Lemma v_scode_helper : exists (f : v_encT X n) (phi : v_decT X n) , 
                         (forall x, phi (f x) = x) /\
                         (exp_len_cw f P) / (INR n) < (`H P + epsilon).
Proof.
exists (f P epsilon') .
exists (phi n' P epsilon').
split=> [ x |]; first  by apply (phi_f _ ep'_pos).
apply (Rmult_lt_reg_r (INR n)).
  by apply lt_0_INR; apply /ltP.
rewrite /Rdiv -mulRA -(mulRC (INR n)).
rewrite Rinv_r; last by apply n_non0.
rewrite mulR1 Hexp_len_cw rsum_type_set (rsum_S_not_S _ (`TS P n epsilon')).
rewrite f_typ_notin f_typ_in; last apply ep'_pos.
eapply Rle_lt_trans.
  apply theorem_helper; first apply ep'_pos.
  by apply n0_n_3.
rewrite /L_0 /L_1.
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
rewrite /Rdiv Rinv_r_simpl_l; last first.
  by apply n0_n_helper1.
eapply Rle_lt_trans.
  apply Rplus_le_compat; last by apply Rlt_le, n0_n_1.
    by apply Rplus_le_compat; by [apply Rlt_le, n0_n_2 | apply Rle_refl].
rewrite (_ : _ / _ + _ / _ + _ / _ = epsilon * ( / 4 + / 3 + / 3)) ; last field.
rewrite -{2}(mulR1 epsilon).
apply Rmult_lt_compat_l; first by apply ep_pos.
fourier.
Qed.

End main.

Section variable_length_source_coding.

Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : 0 < epsilon .
(*Definition n0 := maxn (Z.to_nat (ceil (INR 2 / (INR 1 + log (INR #|X|))))) 
                     (maxn (Z.to_nat (ceil (8 / epsilon)))
                     (Z.to_nat (ceil (aep_sigma2 P/ epsilon' ^ 3)))).*)
Local Notation "'n0'" := (n0 P epsilon).


Theorem vscode : (n0 < n)%nat -> 
  exists f : v_encT X n,
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
