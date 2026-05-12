From zoo Require Import
  prelude.
From zoo.common Require Import
  list
  math.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base.
From zoo Require Import
  options.

Implicit Types n : nat.
Implicit Types i : Z.
Implicit Types l : location.
Implicit Types v : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Section chunk_model.
    Definition chunk_model l (i : Z) dq vs : iProp Σ :=
      [∗ list] k ↦ v ∈ vs, l ↦[i + Z.of_nat k]{dq} v.

    #[global] Instance chunk_model_timeless l i dq vs :
      Timeless (chunk_model l i dq vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_model_persistent l i vs :
      Persistent (chunk_model l i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_model_fractional l i vs :
      Fractional (λ q, chunk_model l i (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_model_as_fractional l i q vs :
      AsFractional (chunk_model l i (DfracOwn q) vs) (λ q, chunk_model l i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_model_nil l i dq :
      ⊢ chunk_model l i dq [].
    Proof.
      rewrite /chunk_model //.
    Qed.

    Lemma chunk_model_singleton l dq v :
      l ↦{dq} v ⊣⊢
      chunk_model l 0 dq [v].
    Proof.
      rewrite /chunk_model big_sepL_singleton /=. done.
    Qed.
    Lemma chunk_model_singleton_1 l dq v :
      l ↦{dq} v ⊢
      chunk_model l 0 dq [v].
    Proof.
      rewrite chunk_model_singleton //.
    Qed.
    Lemma chunk_model_singleton_2 l dq v :
      chunk_model l 0 dq [v] ⊢
      l ↦{dq} v.
    Proof.
      rewrite chunk_model_singleton //.
    Qed.

    Lemma chunk_model_app l (i : Z) dq vs1 vs2 :
      chunk_model l i dq vs1 ∗
      chunk_model l (i + length vs1) dq vs2 ⊣⊢
      chunk_model l i dq (vs1 ++ vs2).
    Proof.
      rewrite /chunk_model big_sepL_app. apply bi.sep_proper; first done.
      apply big_sepL_proper. intros ? ? ?.
      rewrite Nat2Z.inj_add Z.add_assoc //.
    Qed.
    Lemma chunk_model_app_1 dq l i vs1 vs2 :
      chunk_model l i dq vs1 -∗
      chunk_model l (i + length vs1) dq vs2 -∗
      chunk_model l i dq (vs1 ++ vs2).
    Proof.
      rewrite -chunk_model_app. iSteps.
    Qed.
    Lemma chunk_model_app_2 {l i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      chunk_model l i dq vs ⊢
        chunk_model l i dq vs1 ∗
        chunk_model l (i + length vs1) dq vs2.
    Proof.
      intros ->. rewrite chunk_model_app //.
    Qed.

    Lemma chunk_model_app3 l (i : Z) dq vs1 vs2 vs3 :
      chunk_model l i dq vs1 ∗
      chunk_model l (i + length vs1) dq vs2 ∗
      chunk_model l (i + length vs1 + length vs2) dq vs3 ⊣⊢
      chunk_model l i dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite -!chunk_model_app //.
    Qed.
    Lemma chunk_model_app3_1 dq l i vs1 vs2 vs3 :
      chunk_model l i dq vs1 -∗
      chunk_model l (i + length vs1) dq vs2 -∗
      chunk_model l (i + length vs1 + length vs2) dq vs3 -∗
      chunk_model l i dq (vs1 ++ vs2 ++ vs3).
    Proof.
      rewrite -chunk_model_app3. iSteps.
    Qed.
    Lemma chunk_model_app3_2 {l i dq vs} vs1 vs2 vs3 :
      vs = vs1 ++ vs2 ++ vs3 →
      chunk_model l i dq vs ⊢
        chunk_model l i dq vs1 ∗
        chunk_model l (i + length vs1) dq vs2 ∗
        chunk_model l (i + length vs1 + length vs2) dq vs3.
    Proof.
      intros ->. rewrite chunk_model_app3 //.
    Qed.

    Lemma chunk_model_atomize l (i : Z) dq vs :
      chunk_model l i dq vs ⊣⊢
      [∗ list] k ↦ v ∈ vs, chunk_model l (i + k) dq [v].
    Proof.
      revert i. induction vs as [|v vs IH]; intros i.
      - rewrite big_sepL_nil. iSplit; iIntros; first done.
        iApply chunk_model_nil.
      - change (v :: vs) with ([v] ++ vs).
        rewrite -chunk_model_app big_sepL_app big_sepL_singleton /=.
        rewrite Z.add_0_r IH.
        apply bi.sep_proper; first done.
        apply big_sepL_proper. intros k x _.
        f_equiv. lia.
    Qed.

    Lemma chunk_model_cons l i dq v vs :
      l ↦[i]{dq} v ∗
      chunk_model l (i + 1) dq vs ⊣⊢
      chunk_model l i dq (v :: vs).
    Proof.
      rewrite /chunk_model /=. f_equiv.
      { rewrite Z.add_0_r //. }
      apply big_sepL_proper. intros ? ? ?.
      rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_assoc //.
    Qed.
    Lemma chunk_model_cons_1 l i dq v vs :
      l ↦[i]{dq} v -∗
      chunk_model l (i + 1) dq vs -∗
      chunk_model l i dq (v :: vs).
    Proof.
      rewrite -chunk_model_cons. iSteps.
    Qed.
    Lemma chunk_model_cons_2 l i dq v vs :
      chunk_model l i dq (v :: vs) ⊢
        l ↦[i]{dq} v ∗
        chunk_model l (i + 1) dq vs.
    Proof.
      rewrite chunk_model_cons //.
    Qed.
    #[global] Instance chunk_model_cons_frame l i dq v vs R Q :
      Frame false R (l ↦[i]{dq} v ∗ chunk_model l (i + 1) dq vs) Q →
      Frame false R (chunk_model l i dq (v :: vs)) Q
    | 2.
    Proof.
      rewrite /Frame chunk_model_cons //.
    Qed.

    Lemma chunk_model_update {l i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_model l i dq vs ⊢
        l ↦[j]{dq} v ∗
        ( ∀ w,
          l ↦[j]{dq} w -∗
          chunk_model l i dq (<[k := w]> vs)
        ).
    Proof.
      intros Hij Hlookup ->.
      rewrite /chunk_model.
      iIntros "H".
      iDestruct (big_sepL_insert_acc with "H") as "(H↦ & H)"; first done.
      replace (i + Z.of_nat ₊ (j - i))%Z with j by lia.
      iSteps.
    Qed.
    Lemma chunk_model_lookup_acc {l i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_model l i dq vs ⊢
        l ↦[j]{dq} v ∗
        ( l ↦[j]{dq} v -∗
          chunk_model l i dq vs
        ).
    Proof.
      intros Hij Hlookup ->.
      rewrite /chunk_model.
      iIntros "H".
      iDestruct (big_sepL_lookup_acc with "H") as "(H↦ & H)"; first done.
      replace (i + Z.of_nat ₊ (j - i))%Z with j by lia.
      iSteps.
    Qed.
    Lemma chunk_model_lookup {l i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_model l i dq vs ⊢
      l ↦[j]{dq} v.
    Proof.
      intros Hij Hlookup ->.
      rewrite /chunk_model.
      iIntros "H".
      iDestruct (big_sepL_lookup with "H") as "H↦"; first done.
      replace (i + Z.of_nat ₊ (j - i))%Z with j by lia.
      done.
    Qed.

    Lemma chunk_model_update' {l i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_model l i dq vs ⊢
        l ↦[j]{dq} v ∗
        ( ∀ w,
          l ↦[j]{dq} w -∗
          chunk_model l i dq (<[k := w]> vs)
        ).
    Proof.
      apply chunk_model_update.
    Qed.
    Lemma chunk_model_lookup_acc' {l i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_model l i dq vs ⊢
        l ↦[j]{dq} v ∗
        ( l ↦[j]{dq} v -∗
          chunk_model l i dq vs
        ).
    Proof.
      apply chunk_model_lookup_acc.
    Qed.
    Lemma chunk_model_lookup' {l i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_model l i dq vs ⊢
      l ↦[j]{dq} v.
    Proof.
      apply chunk_model_lookup.
    Qed.

    Lemma chunk_model_valid l i dq vs :
      0 < length vs →
      chunk_model l i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros Hvs. destruct vs as [| v vs]; first naive_solver lia.
      iIntros "(H↦ & _)".
      iApply (pointsto_valid with "H↦").
    Qed.
    Lemma chunk_model_combine l (i : Z) dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_model l i dq1 vs1 -∗
      chunk_model l i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        chunk_model l i (dq1 ⋅ dq2) vs1.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (l i vs2); iIntros "% Hmodel1 Hmodel2".
      - rewrite (nil_length_inv vs2) //. naive_solver.
      - destruct vs2 as [| v2 vs2]; first done.
        iDestruct (chunk_model_cons_2 with "Hmodel1") as "(H↦1 & Hmodel1)".
        iDestruct (chunk_model_cons_2 with "Hmodel2") as "(H↦2 & Hmodel2)".
        iDestruct (pointsto_combine with "H↦1 H↦2") as "(-> & H↦)".
        iDestruct ("IH" with "[] Hmodel1 Hmodel2") as "(-> & Hmodel)"; first iSteps. iSplit; first iSteps.
        iApply (chunk_model_cons_1 with "H↦ Hmodel").
    Qed.
    Lemma chunk_model_valid_2 l dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l 0 dq1 vs1 -∗
      chunk_model l 0 dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(-> & Hmodel)"; first done.
      iDestruct (chunk_model_valid with "Hmodel") as "$"; first done.
      iSteps.
    Qed.
    Lemma chunk_model_agree l dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_model l 0 dq1 vs1 -∗
      chunk_model l 0 dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "($ & _)"; first done.
    Qed.
    Lemma chunk_model_dfrac_ne l1 dq1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_model l1 0 dq1 vs1 -∗
      chunk_model l2 0 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hmodel1 Hmodel2" (->).
      iDestruct (chunk_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma chunk_model_ne l1 vs1 l2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l1 0 (DfracOwn 1) vs1 -∗
      chunk_model l2 0 dq2 vs2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros.
      iApply chunk_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_model_exclusive l vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_model l 0 (DfracOwn 1) vs1 -∗
      chunk_model l 0 dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (chunk_model_ne with "Hmodel1 Hmodel2") as %?; done.
    Qed.
    Lemma chunk_model_persist l i dq vs :
      chunk_model l i dq vs ⊢ |==>
      chunk_model l i DfracDiscarded vs.
    Proof.
      iIntros "Hmodel".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hmodel").
      iIntros "!> %k %v %Hk H".
      iApply (pointsto_persist with "H").
    Qed.
  End chunk_model.

  Section chunk_span.
    Definition chunk_span l (i : Z) dq n : iProp Σ :=
      ∃ vs,
      ⌜length vs = n⌝ ∗
      chunk_model l i dq vs.

    #[global] Instance chunk_span_timeless l dq n :
      Timeless (chunk_span l 0 dq n).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_span_persistent l n :
      Persistent (chunk_span l 0 DfracDiscarded n).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_span_fractional l n :
      Fractional (λ q, chunk_span l 0 (DfracOwn q) n).
    Proof.
      intros q1 q2. rewrite /chunk_span. setoid_rewrite chunk_model_fractional. iSplit; first iSteps.
      iIntros "((%vs & % & Hmodel1) & (%_vs & % & Hmodel2))".
      iDestruct (chunk_model_agree with "Hmodel1 Hmodel2") as %<-; first naive_solver.
      iSteps.
    Qed.
    #[global] Instance chunk_span_as_fractional l q n :
      AsFractional (chunk_span l 0 (DfracOwn q) n) (λ q, chunk_span l 0 (DfracOwn q) n) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_span_singleton l dq :
      ( ∃ v,
        l ↦{dq} v
      ) ⊣⊢
      chunk_span l 0 dq 1.
    Proof.
      setoid_rewrite chunk_model_singleton. iSplit.
      - iIntros "(%v & Hmodel)".
        iExists [v]. iSteps.
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v []]; try done. iSteps.
    Qed.
    Lemma chunk_span_singleton_1 l dq v :
      l ↦{dq} v ⊢
      chunk_span l 0 dq 1.
    Proof.
      rewrite -chunk_span_singleton. iSteps.
    Qed.
    Lemma chunk_span_singleton_2 l dq :
      chunk_span l 0 dq 1 ⊢
        ∃ v,
        l ↦{dq} v.
    Proof.
      rewrite chunk_span_singleton. iSteps.
    Qed.

    Lemma chunk_span_cons l dq n :
      ( ∃ v,
        l ↦{dq} v ∗
        chunk_span l 1 dq n
      ) ⊣⊢
      chunk_span l 0 dq (S n).
    Proof.
      iSplit.
      - iIntros "(%v & H↦ & (%vs & % & Hmodel))".
        iExists (v :: vs). iSplit; first iSteps.
        iApply (chunk_model_cons_1 with "H↦ Hmodel").
      - iIntros "(%vs & % & Hmodel)".
        destruct vs as [| v vs]; first done.
        iDestruct (chunk_model_cons_2 with "Hmodel") as "(H↦ & Hmodel)".
        iExists v. iFrameSteps.
    Qed.
    Lemma chunk_span_cons_1 l dq v n :
      l ↦{dq} v -∗
      chunk_span l 1 dq n -∗
      chunk_span l 0 dq (S n).
    Proof.
      rewrite -chunk_span_cons. iSteps.
    Qed.
    Lemma chunk_span_cons_2 l dq n :
      chunk_span l 0 dq (S n) ⊢
        ∃ v,
        l ↦{dq} v ∗
        chunk_span l 1 dq n.
    Proof.
      rewrite chunk_span_cons //.
    Qed.
    #[global] Instance chunk_span_cons_frame l dq v n R Q :
      Frame false R (l ↦{dq} v ∗ chunk_span l 1 dq n) Q →
      Frame false R (chunk_span l 0 dq (S n)) Q
    | 2.
    Proof.
      rewrite /Frame. setoid_rewrite <- chunk_span_cons. intros H.
      iPoseProof H as "H". iSteps.
    Qed.

    Lemma chunk_span_app l (i : Z) dq n1 n2 :
      chunk_span l i dq n1 ∗
      chunk_span l (i + n1) dq n2 ⊣⊢
      chunk_span l i dq (n1 + n2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & %Hvs1 & Hmodel1) & (%vs2 & %Hvs2 & Hmodel2))".
        iExists (vs1 ++ vs2). iSplit; first (simpl_length; naive_solver).
        rewrite -Hvs1.
        iApply (chunk_model_app_1 with "Hmodel1 Hmodel2").
      - iIntros "(%vs & %Hvs & Hmodel)".
        iDestruct (chunk_model_app_2 (take n1 vs) (drop n1 vs) (eq_sym (take_drop _ _)) with "Hmodel") as "(Hmodel1 & Hmodel2)".
        assert (length (take n1 vs) = n1) as Hlen by (rewrite length_take_le //; lia).
        iSplitL "Hmodel1".
        + iExists (take n1 vs). iFrame. iPureIntro. done.
        + iExists (drop n1 vs). iFrame. iSplit; first (iPureIntro; rewrite length_drop; lia).
          rewrite Hlen //.
    Qed.
    Lemma chunk_span_app_1 dq l (i : Z) n1 n2 :
      chunk_span l i dq n1 -∗
      chunk_span l (i + n1) dq n2 -∗
      chunk_span l i dq (n1 + n2).
    Proof.
      rewrite -chunk_span_app. iSteps.
    Qed.
    Lemma chunk_span_app_2 {l i dq n} n1 n2 :
      n = n1 + n2 →
      chunk_span l i dq n ⊢
        chunk_span l i dq n1 ∗
        chunk_span l (i + n1) dq n2.
    Proof.
      intros ->. rewrite chunk_span_app //.
    Qed.

    Lemma chunk_span_app3 l (i : Z) dq n1 n2 n3 :
      chunk_span l i dq n1 ∗
      chunk_span l (i + n1) dq n2 ∗
      chunk_span l (i + n1 + n2) dq n3 ⊣⊢
      chunk_span l i dq (n1 + n2 + n3).
    Proof.
      rewrite (chunk_span_app _ (i + n1) _ n2 n3).
      rewrite chunk_span_app Nat.add_assoc //.
    Qed.
    Lemma chunk_span_app3_1 dq l (i : Z) n1 n2 n3 :
      chunk_span l i dq n1 -∗
      chunk_span l (i + n1) dq n2 -∗
      chunk_span l (i + n1 + n2) dq n3 -∗
      chunk_span l i dq (n1 + n2 + n3).
    Proof.
      rewrite -chunk_span_app3. iSteps.
    Qed.
    Lemma chunk_span_app3_2 {l i dq n} n1 n2 n3 :
      n = n1 + n2 + n3 →
      chunk_span l i dq n ⊢
        chunk_span l i dq n1 ∗
        chunk_span l (i + n1) dq n2 ∗
        chunk_span l (i + n1 + n2) dq n3.
    Proof.
      intros ->. rewrite chunk_span_app3 //.
    Qed.

    Lemma chunk_span_update {l i dq n} (j : Z) :
      (i ≤ j < i + n)%Z →
      chunk_span l i dq n ⊢
        ∃ v,
        l ↦[j]{dq} v ∗
        ( ∀ w,
          l ↦[j]{dq} w -∗
          chunk_span l i dq n
        ).
    Proof.
      iIntros "%Hi (%vs & %Hvs & Hmodel)".
      set k := ₊(j - i).
      assert (vs !! k = Some (vs !!! k)) as Hk.
      { rewrite list_lookup_lookup_total_lt //. subst k. lia. }
      iDestruct (chunk_model_update j k with "Hmodel") as "(H↦ & Hmodel)"; [lia | done | done |].
      iExists (vs !!! k). iFrame. iIntros "%w H↦".
      iSpecialize ("Hmodel" with "H↦").
      iExists (<[k := w]> vs). iFrame. iPureIntro. rewrite length_insert //.
    Qed.
    Lemma chunk_span_lookup_acc {l i dq n} (j : Z) :
      (i ≤ j < i + n)%Z →
      chunk_span l i dq n ⊢
        ∃ v,
        l ↦[j]{dq} v ∗
        ( l ↦[j]{dq} v -∗
          chunk_span l i dq n
        ).
    Proof.
      iIntros "%Hi Hspan".
      iDestruct (chunk_span_update with "Hspan") as "(%v & H↦ & Hspan)"; first done.
      auto with iFrame.
    Qed.
    Lemma chunk_span_lookup {l i dq n} (j : Z) :
      (i ≤ j < i + n)%Z →
      chunk_span l i dq n ⊢
        ∃ v,
        l ↦[j]{dq} v.
    Proof.
      iIntros "%Hi Hspan".
      iDestruct (chunk_span_lookup_acc with "Hspan") as "(%v & H↦ & _)"; first done.
      iSteps.
    Qed.

    Lemma chunk_span_update' {l i dq n} (j : Z) :
      (i ≤ j < i + n)%Z →
      chunk_span l i dq n ⊢
        ∃ v,
        l ↦[j]{dq} v ∗
        ( ∀ w,
          l ↦[j]{dq} w -∗
          chunk_span l i dq n
        ).
    Proof.
      apply chunk_span_update.
    Qed.
    Lemma chunk_span_lookup_acc' {l i dq n} (j : Z) :
      (i ≤ j < i + n)%Z →
      chunk_span l i dq n ⊢
        ∃ v,
        l ↦[j]{dq} v ∗
        ( l ↦[j]{dq} v -∗
          chunk_span l i dq n
        ).
    Proof.
      apply chunk_span_lookup_acc.
    Qed.
    Lemma chunk_span_lookup' {l i dq n} (j : Z) :
      (i ≤ j < i + n)%Z →
      chunk_span l i dq n ⊢
        ∃ v,
        l ↦[j]{dq} v.
    Proof.
      apply chunk_span_lookup.
    Qed.

    Lemma chunk_span_valid l dq n :
      0 < n →
      chunk_span l 0 dq n ⊢
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%vs & % & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first naive_solver.
    Qed.
    Lemma chunk_span_combine l dq1 n1 dq2 n2 :
      n1 = n2 →
      chunk_span l 0 dq1 n1 -∗
      chunk_span l 0 dq2 n2 -∗
      chunk_span l 0 (dq1 ⋅ dq2) n1.
    Proof.
      iIntros (<-) "(%vs1 & % & Hmodel1) (%vs2 & % & Hmodel2)".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)"; first naive_solver.
      iSteps.
    Qed.
    Lemma chunk_span_valid_2 l dq1 n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk_span l 0 dq1 n1 -∗
      chunk_span l 0 dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk_span_combine with "Hspan1 Hspan2") as "Hspan"; first done.
      iDestruct (chunk_span_valid with "Hspan") as "$"; first done.
    Qed.
    Lemma chunk_span_dfrac_ne l1 dq1 n1 l2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_span l1 0 dq1 n1 -∗
      chunk_span l2 0 dq2 n2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      iIntros "% % % Hspan1 Hspan2" (->).
      iDestruct (chunk_span_valid_2 with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk_span_ne l1 n1 l2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk_span l1 0 (DfracOwn 1) n1 -∗
      chunk_span l2 0 dq2 n2 -∗
      ⌜l1 ≠ l2⌝.
    Proof.
      intros.
      iApply chunk_span_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_span_exclusive l n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      chunk_span l 0 (DfracOwn 1) n1 -∗
      chunk_span l 0 dq2 n2 -∗
      False.
    Proof.
      iIntros "% % Hspan1 Hspan2".
      iDestruct (chunk_span_ne with "Hspan1 Hspan2") as %?; done.
    Qed.
    Lemma chunk_span_persist l dq n :
      chunk_span l 0 dq n ⊢ |==>
      chunk_span l 0 DfracDiscarded n.
    Proof.
      iIntros "(%vs & % & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iSteps.
    Qed.
  End chunk_span.

  Section chunk_cslice.
    Implicit Types sz : nat.

    Definition chunk_cslice l sz (i : Z) dq vs : iProp Σ :=
      [∗ list] k ↦ v ∈ vs, l ↦[(i + k) `mod` sz]{dq} v.

    #[global] Instance chunk_cslice_timeless l sz i dq vs :
      Timeless (chunk_cslice l sz i dq vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_cslice_persistent l sz i vs :
      Persistent (chunk_cslice l sz i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance chunk_cslice_fractional l sz i vs :
      Fractional (λ q, chunk_cslice l sz i (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance chunk_cslice_as_fractionak l sz i q vs :
      AsFractional (chunk_cslice l sz i (DfracOwn q) vs) (λ q, chunk_cslice l sz i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma chunk_model_to_cslice l dq vs :
      chunk_model l 0 dq vs ⊢
      chunk_cslice l (length vs) 0 dq vs.
    Proof.
      iIntros "Hmodel".
      iApply (big_sepL_impl with "Hmodel"). iIntros (k v Hk%lookup_lt_Some) "!> H↦".
      rewrite Z.add_0_l Z.mod_small //; first lia.
    Qed.
    Lemma chunk_model_cslice_cell l i sz dq v :
      chunk_model l (i `mod` sz) dq [v] ⊣⊢
      chunk_cslice l sz i dq [v].
    Proof.
      rewrite /chunk_model /chunk_cslice.
      rewrite !big_sepL_singleton /= Z.add_0_r right_id //.
    Qed.

    Lemma chunk_cslice_nil l sz i dq :
      ⊢ chunk_cslice l sz i dq [].
    Proof.
      rewrite /chunk_cslice //.
    Qed.

    Lemma chunk_cslice_singleton l sz i dq v :
      l ↦[i `mod` sz]{dq} v ⊣⊢
      chunk_cslice l sz i dq [v].
    Proof.
      rewrite /chunk_cslice big_sepL_singleton /= Z.add_0_r //.
    Qed.
    Lemma chunk_cslice_singleton_1 l sz i dq v :
      l ↦[i `mod` sz]{dq} v ⊢
      chunk_cslice l sz i dq [v].
    Proof.
      rewrite chunk_cslice_singleton //.
    Qed.
    Lemma chunk_cslice_singleton_2 l sz i dq v :
      chunk_cslice l sz i dq [v] ⊢
      l ↦[i `mod` sz]{dq} v.
    Proof.
      rewrite chunk_cslice_singleton //.
    Qed.

    Lemma chunk_cslice_app l sz i dq vs1 vs2 :
      chunk_cslice l sz i dq vs1 ∗
      chunk_cslice l sz (i + length vs1) dq vs2 ⊣⊢
      chunk_cslice l sz i dq (vs1 ++ vs2).
    Proof.
      rewrite /chunk_cslice big_sepL_app.
      apply bi.sep_proper; first done.
      apply big_sepL_proper. intros k v _.
      rewrite Nat2Z.inj_add Z.add_assoc //.
    Qed.
    Lemma chunk_cslice_app_1 l sz dq (i1 : Z) vs1 (i2 : Z) vs2 :
      i2 = (i1 + length vs1)%Z →
      chunk_cslice l sz i1 dq vs1 -∗
      chunk_cslice l sz i2 dq vs2 -∗
      chunk_cslice l sz i1 dq (vs1 ++ vs2).
    Proof.
      intros ->. rewrite -chunk_cslice_app. iSteps.
    Qed.
    Lemma chunk_cslice_app_2 {l sz i dq vs} vs1 vs2 :
      vs = vs1 ++ vs2 →
      chunk_cslice l sz i dq vs ⊢
        chunk_cslice l sz i dq vs1 ∗
        chunk_cslice l sz (i + length vs1) dq vs2.
    Proof.
      rewrite chunk_cslice_app. iSteps.
    Qed.

    Lemma chunk_cslice_app3 {l sz i dq vs} n1 (i1 : Z) n2 (i2 : Z) :
      i1 = (i + n1)%Z →
      i2 = (i1 + n2)%Z →
      n1 ≤ length vs →
      n1 + n2 ≤ length vs →
      chunk_cslice l sz i dq vs ⊣⊢
        chunk_cslice l sz i dq (take n1 vs) ∗
        chunk_cslice l sz i1 dq (take n2 $ drop n1 vs) ∗
        chunk_cslice l sz i2 dq (drop (n1 + n2) vs).
    Proof.
      intros -> -> ? ?.
      rewrite -{1}(take_drop n1 vs).
      rewrite -{1}(take_drop n2 (drop n1 vs)) drop_drop.
      rewrite -!chunk_cslice_app. simpl_length.
      rewrite !Nat.min_l //; first lia.
    Qed.

    Lemma chunk_cslice_cons l sz i dq v vs :
      l ↦[i `mod` sz]{dq} v ∗
      chunk_cslice l sz (i + 1) dq vs ⊣⊢
      chunk_cslice l sz i dq (v :: vs).
    Proof.
      assert (v :: vs = [v] ++ vs) as -> by done.
      rewrite -chunk_cslice_app chunk_cslice_singleton /=. done.
    Qed.
    Lemma chunk_cslice_cons_1 l sz i dq v vs :
      l ↦[i `mod` sz]{dq} v -∗
      chunk_cslice l sz (i + 1) dq vs -∗
      chunk_cslice l sz i dq (v :: vs).
    Proof.
      rewrite -chunk_cslice_cons. iSteps.
    Qed.
    Lemma chunk_cslice_cons_2 l sz i dq v vs :
      chunk_cslice l sz i dq (v :: vs) ⊢
        l ↦[i `mod` sz]{dq} v ∗
        chunk_cslice l sz (i + 1) dq vs.
    Proof.
      rewrite chunk_cslice_cons //.
    Qed.

    Lemma chunk_cslice_update {l sz i dq vs} (k : nat) v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
        l ↦[(i + k) `mod` sz]{dq} v ∗
        ( ∀ w,
          l ↦[(i + k) `mod` sz]{dq} w -∗
          chunk_cslice l sz i dq (<[k := w]> vs)
        ).
    Proof.
      apply: big_sepL_insert_acc.
    Qed.
    Lemma chunk_cslice_lookup_acc {l sz i dq vs} (k : nat) v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
        l ↦[(i + k) `mod` sz]{dq} v ∗
        ( l ↦[(i + k) `mod` sz]{dq} v -∗
          chunk_cslice l sz i dq vs
        ).
    Proof.
      apply: big_sepL_lookup_acc.
    Qed.
    Lemma chunk_cslice_lookup {l sz i dq vs} (k : nat) v :
      vs !! k = Some v →
      chunk_cslice l sz i dq vs ⊢
      l ↦[(i + k) `mod` sz]{dq} v.
    Proof.
      apply: big_sepL_lookup.
    Qed.

    Lemma chunk_cslice_update' {l sz i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_cslice l sz i dq vs ⊢
        l ↦[j `mod` sz]{dq} v ∗
        ( ∀ w,
          l ↦[j `mod` sz]{dq} w -∗
          chunk_cslice l sz i dq (<[k := w]> vs)
        ).
    Proof.
      intros Hij Hlookup ->.
      rewrite {1}(chunk_cslice_update _ _ Hlookup).
      replace ((i + Z.of_nat ₊ (j - i))%Z) with j by lia. done.
    Qed.
    Lemma chunk_cslice_lookup_acc' {l sz i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_cslice l sz i dq vs ⊢
        l ↦[j `mod` sz]{dq} v ∗
        ( l ↦[j `mod` sz]{dq} v -∗
          chunk_cslice l sz i dq vs
        ).
    Proof.
      intros Hij Hlookup ->.
      rewrite {1}(chunk_cslice_lookup_acc _ _ Hlookup).
      replace ((i + Z.of_nat ₊ (j - i))%Z) with j by lia. done.
    Qed.
    Lemma chunk_cslice_lookup' {l sz i dq vs} (j : Z) k v :
      (i ≤ j)%Z →
      vs !! k = Some v →
      k = ₊(j - i) →
      chunk_cslice l sz i dq vs ⊢
      l ↦[j `mod` sz]{dq} v.
    Proof.
      intros Hij Hlookup ->.
      rewrite {1}(chunk_cslice_lookup _ _ Hlookup).
      replace ((i + Z.of_nat ₊ (j - i))%Z) with j by lia. done.
    Qed.

    Lemma chunk_cslice_shift l sz i dq vs :
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i + sz) dq vs.
    Proof.
      rewrite /chunk_cslice. apply big_sepL_proper. intros k v _.
      assert ((i + sz + Z.of_nat k) `mod` sz = (i + Z.of_nat k) `mod` sz)%Z as Heq.
      { rewrite -Z.add_assoc (Z.add_comm (Z.of_nat sz) (Z.of_nat k)) Z.add_assoc.
        rewrite -Zplus_mod_idemp_r Z_mod_same_full Z.add_0_r //. }
      rewrite Heq //.
    Qed.

    Lemma chunk_cslice_shift_right l sz i dq vs :
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i + sz) dq vs.
    Proof.
      rewrite chunk_cslice_shift //.
    Qed.

    Lemma chunk_cslice_shift_left l sz i dq vs :
      (sz ≤ i)%Z →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i - sz) dq vs.
    Proof.
      intros.
      rewrite (chunk_cslice_shift _ _ (i - sz)).
      replace ((i - sz + sz))%Z with i by lia. done.
    Qed.

    Lemma chunk_cslice_mod l sz i dq vs :
      0 < sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i `mod` sz) dq vs.
    Proof.
      intros.
      rewrite /chunk_cslice. apply big_sepL_proper. intros k v _.
      assert ((i `mod` sz + Z.of_nat k) `mod` sz = (i + Z.of_nat k) `mod` sz)%Z as Heq.
      { rewrite Z.add_mod_idemp_l //. lia. }
      rewrite Heq //.
    Qed.

    #[local] Lemma chunk_cslice_to_model_aux l sz i dq vs :
      0 < sz →
      (0 ≤ i)%Z →
      (i + length vs ≤ sz)%Z →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_model l i dq vs.
    Proof.
      intros.
      rewrite /chunk_cslice /chunk_model.
      apply big_sepL_proper. intros k v Hk%lookup_lt_Some.
      rewrite Z.mod_small //. lia.
    Qed.
    Lemma chunk_cslice_to_model l sz i dq vs :
      0 < sz →
      length vs ≤ sz →
      chunk_cslice l sz i dq vs ⊣⊢
        chunk_model l (i `mod` sz) dq (take (sz - ₊(i `mod` sz)) vs) ∗
        chunk_model l 0 dq (drop (sz - ₊(i `mod` sz)) vs).
    Proof.
    Admitted.
    Lemma chunk_cslice_to_model_full l sz i dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_model l 0 dq (rotation (sz - ₊(i `mod` sz)) vs).
    Proof.
    Admitted.

    Lemma chunk_cslice_rotation_right {l sz i dq vs} n :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz (i + n) dq (rotation (₊(n `mod` sz)) vs).
    Proof.
    Admitted.
    Lemma chunk_cslice_rotation_right_1 {l sz i dq vs} n :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊢
      chunk_cslice l sz (i + n) dq (rotation (₊(n `mod` sz)) vs).
    Proof.
    Admitted.
    Lemma chunk_cslice_rotation_right_0 {l sz dq vs} i :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz 0 dq vs ⊣⊢
      chunk_cslice l sz i dq (rotation (₊(i `mod` sz)) vs).
    Proof.
    Admitted.

    Lemma chunk_cslice_rotation_right' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = (i1 + n)%Z →
      chunk_cslice l sz i1 dq vs ⊣⊢
      chunk_cslice l sz i2 dq (rotation (₊(n `mod` sz)) vs).
    Proof.
    Admitted.
    Lemma chunk_cslice_rotation_right_1' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i2 = (i1 + n)%Z →
      chunk_cslice l sz i1 dq vs ⊢
      chunk_cslice l sz i2 dq (rotation (₊(n `mod` sz)) vs).
    Proof.
    Admitted.

    Lemma chunk_cslice_rotation_left l sz i n dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz (i + n) dq vs ⊣⊢
      chunk_cslice l sz i dq (rotation (sz - ₊(n `mod` sz)) vs).
    Proof.
    Admitted.
    Lemma chunk_cslice_rotation_left_1 l sz i n dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz (i + n) dq vs ⊢
      chunk_cslice l sz i dq (rotation (sz - ₊(n `mod` sz)) vs).
    Proof.
    Admitted.
    Lemma chunk_cslice_rotation_left_0 l sz i dq vs :
      0 < sz →
      length vs = sz →
      chunk_cslice l sz i dq vs ⊣⊢
      chunk_cslice l sz 0 dq (rotation (sz - ₊(i `mod` sz)) vs).
    Proof.
    Admitted.

    Lemma chunk_cslice_rotation_left' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = (i2 + n)%Z →
      chunk_cslice l sz i1 dq vs ⊣⊢
      chunk_cslice l sz i2 dq (rotation (sz - ₊(n `mod` sz)) vs).
    Proof.
    Admitted.
    Lemma chunk_cslice_rotation_left_1' {l sz i1 dq vs} i2 n :
      0 < sz →
      length vs = sz →
      i1 = (i2 + n)%Z →
      chunk_cslice l sz i1 dq vs ⊢
      chunk_cslice l sz i2 dq (rotation (sz - ₊(n `mod` sz)) vs).
    Proof.
    Admitted.

    Lemma chunk_cslice_rebase {l sz i1 dq vs1} i2 :
      0 < sz →
      length vs1 = sz →
      chunk_cslice l sz i1 dq vs1 ⊢
        ∃ vs2 n,
        ⌜vs2 = rotation n vs1⌝ ∗
        chunk_cslice l sz i2 dq vs2 ∗
        ( chunk_cslice l sz i2 dq vs2 -∗
          chunk_cslice l sz i1 dq vs1
        ).
    Proof.
    Admitted.

    Lemma chunk_cslice_valid l sz i dq vs :
      0 < length vs →
      chunk_cslice l sz i dq vs ⊢
      ⌜✓ dq⌝.
    Proof.
      intros Hvs. destruct vs as [| v vs]; first naive_solver lia.
      iIntros "(H↦ & _)".
      iApply (pointsto_valid with "H↦").
    Qed.
    Lemma chunk_cslice_combine l sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_cslice l sz i dq1 vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
        ⌜vs1 = vs2⌝ ∗
        chunk_cslice l sz i (dq1 ⋅ dq2) vs1.
    Proof.
      iInduction vs1 as [| v1 vs1] "IH" forall (i vs2); iIntros "% Hcslice1 Hcslice2".
      - rewrite (nil_length_inv vs2) //. naive_solver.
      - destruct vs2 as [| v2 vs2]; first done.
        iDestruct (chunk_cslice_cons_2 with "Hcslice1") as "(H↦1 & Hcslice1)".
        iDestruct (chunk_cslice_cons_2 with "Hcslice2") as "(H↦2 & Hcslice2)".
        iDestruct (pointsto_combine with "H↦1 H↦2") as "(-> & H↦)".
        iDestruct ("IH" with "[] Hcslice1 Hcslice2") as "(-> & Hcslice)"; first iSteps. iSplit; first iSteps.
        iApply (chunk_cslice_cons_1 with "H↦ Hcslice").
    Qed.
    Lemma chunk_cslice_valid_2 l sz i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_cslice l sz i dq1 vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_combine with "Hcslice1 Hcslice2") as "(-> & Hcslice)"; first done.
      iDestruct (chunk_cslice_valid with "Hcslice") as "$"; first done.
      iSteps.
    Qed.
    Lemma chunk_cslice_agree l sz i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      chunk_cslice l sz i dq1 vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_combine with "Hcslice1 Hcslice2") as "(-> & _)"; first done.
      iSteps.
    Qed.
    Lemma chunk_cslice_dfrac_ne l sz i1 dq1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      chunk_cslice l sz i1 dq1 vs1 -∗
      chunk_cslice l sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      iIntros "% % % Hcslice1 Hcslice2" (->).
      iDestruct (chunk_cslice_valid_2 with "Hcslice1 Hcslice2") as %?; naive_solver.
    Qed.
    Lemma chunk_cslice_ne l sz i1 vs1 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_cslice l sz i1 (DfracOwn 1) vs1 -∗
      chunk_cslice l sz i2 dq2 vs2 -∗
      ⌜i1 ≠ i2⌝.
    Proof.
      intros.
      iApply chunk_cslice_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma chunk_cslice_exclusive l sz i vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      chunk_cslice l sz i (DfracOwn 1) vs1 -∗
      chunk_cslice l sz i dq2 vs2 -∗
      False.
    Proof.
      iIntros "% % Hcslice1 Hcslice2".
      iDestruct (chunk_cslice_ne with "Hcslice1 Hcslice2") as %?; done.
    Qed.
    Lemma chunk_cslice_persist l sz i dq vs :
      chunk_cslice l sz i dq vs ⊢ |==>
      chunk_cslice l sz i DfracDiscarded vs.
    Proof.
      iIntros "Hcslice".
      iApply big_sepL_bupd. iApply (big_sepL_impl with "Hcslice").
      iIntros "!> %k %v %Hk H↦". iApply (pointsto_persist with "H↦").
    Qed.

    Lemma chunk_cslice_length l sz i vs :
      0 < sz →
      chunk_cslice l sz i (DfracOwn 1) vs ⊢
      ⌜length vs ≤ sz⌝.
    Proof.
    Admitted.
  End chunk_cslice.

  Section itype_chunk.
    Definition itype_chunk τ `{!iType _ τ} sz l : iProp Σ :=
      inv nroot (
        ∃ vs,
        ⌜sz = length vs⌝ ∗
        chunk_model l 0 (DfracOwn 1) vs ∗
        [∗ list] v ∈ vs, τ v
      ).

    #[global] Instance itype_chunk_persistent τ `{!iType _ τ} sz l :
      Persistent (itype_chunk τ sz l).
    Proof.
      apply _.
    Qed.

    Lemma itype_chunk_0 τ `{!iType _ τ} l :
      ⊢ |={⊤}=>
        itype_chunk τ 0 l.
    Proof.
      iApply inv_alloc. iExists []. iSteps.
    Qed.

    Lemma itype_chunk_shift (i : Z) τ `{!iType _ τ} (sz : nat) l :
      (0 ≤ i ≤ sz)%Z →
      itype_chunk τ sz l ⊢
      itype_chunk τ (sz - ₊i) (l +ₗ i).
    Proof.
    Admitted.

    Lemma itype_chunk_le sz' τ `{!iType _ τ} sz l :
      (sz' ≤ sz) →
      itype_chunk τ sz l ⊢
      itype_chunk τ sz' l.
    Proof.
    Admitted.
  End itype_chunk.
End zoo_G.

#[global] Opaque chunk_model.
#[global] Opaque chunk_span.
#[global] Opaque chunk_cslice.
