import category_theory.category
import category_theory.functor
import category_theory.types
import help_functions

import tactic.tidy


namespace diagram_lemmas

universe u

open classical function set category_theory help_functions


local notation f ` ⊚ ` :80 g:80 := category_struct.comp g f

variables {F : Type u ⥤ Type u} 
        {A B C : Type u}


lemma diagram_injective (f: B ⟶ A)
                        (g: C ⟶ A)
                        (inj : injective f)
                        : (∃! h : C ⟶ B , f ∘ h = g) ↔ 
                          (range g ⊆ range f) 
    := 
        iff.intro 
        begin
            tidy
        end
        begin
            assume im,
            let G : C → B → Prop := λ c b , g c = f b, 
            have G1 :  ∀ c : C , ∃ b : B, G c b 
                    :=
                        have G10 : 
                            ∀ a : A , a ∈ range g → 
                                    a ∈ range f := im,
                        have G11 : 
                            ∀ c : C , g c ∈ range f := 
                                λ c , 
                                have G110 : g c ∈ range g := by tidy,
                                G10 (g c) G110,
                        have G12 : ∀ c : C , ∃ b : B , g c = f b := 
                            λ c : C,  
                            have G110 : g c ∈ range f := G11 c,
                            by tidy,
                        G12,
            have G2 :  ∀ c : C , ∃! b : B, G c b
                    :=
                        λ c, 
                        have G20 : G c (some (G1 c)) := some_spec (G1 c),
                        have G21 : f (some (G1 c)) = g c := 
                            show f (some (G1 c)) = g c,
                            from 
                                have G210 : _ := G c (some (G1 c)),
                                by tidy,
                        have G22 : ∀ b₁ : B, G c b₁ → 
                                    b₁ = (some (G1 c)) := 
                                    λ b₁ : B, assume cbG : G c b₁,
                                    show b₁ = (some (G1 c)), from
                                    have G220 : f b₁ = g c := by tidy,
                                    have G221 : f (some (G1 c)) = f b₁ := by rw [G21 , G220],
                                    eq.symm (inj G221),
                        by tidy,
            let h : C ⟶ B := graph_to_map G G2,
            have G3 : ∀ c , (f ∘ h) c = g c:= 
                assume c,
                have G31 : h c = some (G2 c) := by tidy,
                have G32 : _ := some_spec (G2 c),
                have G33 : G c (some (G2 c)) := and.left G32,
                by tidy,
            have G4 : f ∘ h = g := funext G3,
            have G5 : ∀ h₁ : C ⟶ B , f ∘ h₁ = g → h₁ = h := 
                    assume h₁ fh,
                    have G51 : f ∘ h₁ = f ∘ h := by rw [fh , G4],
                    have G511 : f ⊚ h₁ = f ⊚ h := by tidy,
                    have G52 : mono f := iff.elim_right (mono_iff_injective f) inj,
                    have G53 : _ := G52.right_cancellation,
                    G53 h₁ h G511,
            exact exists_unique.intro h G4 G5
        end



lemma diagram_surjective
            (f : A ⟶ B) 
            (g : A ⟶ C)
            (sur: surjective f) 
            :   (∃! h : B ⟶ C , h ∘ f = g) ↔
                (sub_kern f g) 
    :=
        iff.intro
        begin
            assume ex : ∃ h , (h ∘ f = g ∧ 
                            ∀ h₁, h₁ ∘ f = g → h₁ = h),
            show ∀ a₁ a₂ , kern f a₁  a₂ → kern g a₁ a₂,
            cases ex with h spec,
            exact spec.1 ▸ kern_comp f h
        end
        begin 
            assume k : ∀ a₁ a₂ , f a₁ = f a₂ → g a₁ = g a₂,
            let h : B → C := λ b : B, g (surj_inv sur b),
            have s2 : ∀ a , f (surj_inv sur (f a)) = f a := 
                assume a , surj_inv_eq sur (f a),
            have s3 : ∀ a , g (surj_inv sur (f a)) = g a :=
                assume a , k (surj_inv sur (f a)) a (s2 a),
            have s4 : ∀ a , h (f a) = g a := 
                assume a,
                show g (surj_inv sur (f a)) = g a,
                from s3 a,
            have s5:  h ∘ f = g := funext s4,
            have s6 : ∀ h₂ :B → C , h₂ ∘ f = g → h₂ = h := 
                begin 
                    assume h₂ h2,
                    have s61 : h₂ ∘ f = h ∘ f := by simp [s5 , h2],
                    haveI s62 : epi f := (epi_iff_surjective f).2 sur,
                    have left_cancel := s62.left_cancellation,
                    have s63 : h₂ = h := left_cancel h₂ h s61,
                    tidy
                end,

            exact exists_unique.intro h s5 s6,
        end



end diagram_lemmas