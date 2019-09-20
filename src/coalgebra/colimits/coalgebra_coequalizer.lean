import set_category.diagram_lemmas
import set_category.category_set
import set_category.colimits.Coequalizer
import help_functions
import coalgebra.Coalgebra


import tactic.tidy

universes u



namespace coalgebra_coequalizer

open category_theory 
     set 
     coalgebra
     classical
     help_functions
     Coequalizer
     coalgebra.Coalgebra
     category_set
     

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f




variables   {F : Type u ⥤ Type u}
            {𝔸 Β: Coalgebra F}
            (ϕ ψ : 𝔸 ⟶ Β)


theorem coequalizer_is_homomorphism :
    let Β_Θ := theta ϕ ψ in
    let π_Θ : Β.carrier ⟶ Β_Θ := coequalizer ϕ ψ in
    ∃! α : Β_Θ → (F.obj Β_Θ), 
    @is_coalgebra_homomorphism F Β ⟨Β_Θ , α⟩ π_Θ
    :=  
    begin
        intros Β_Θ π_Θ, 
        
        have hom_f : Β.α ∘ ϕ = (F.map ϕ) ∘ 𝔸.α := ϕ.property,
        have hom_g : Β.α ∘ ψ = (F.map ψ) ∘ 𝔸.α := ψ.property, 
        let ϕ₁  : 𝔸.carrier ⟶ Β.carrier := ϕ.val,
        let ψ₁ : 𝔸.carrier ⟶ Β.carrier := ψ.val,
        have h : is_coequalizer ϕ₁ ψ₁ π_Θ := quot_is_coequalizer ϕ₁ ψ₁,

        have h2 : (F.map π_Θ) ∘ Β.α ∘ ϕ = (F.map π_Θ) ∘ Β.α ∘ ψ :=
            calc (F.map π_Θ) ∘ (Β.α ∘ ϕ)
                     = (F.map π_Θ) ∘ (F.map ϕ) ∘ 𝔸.α         : by rw hom_f
                 ... = ((F.map π_Θ) ⊚ (F.map ϕ)) ∘ 𝔸.α      : rfl
                 ... = (F.map (π_Θ ⊚ ϕ)) ∘ 𝔸.α              : by rw functor.map_comp
                 ... = (F.map (π_Θ ⊚ ψ)) ∘ 𝔸.α              : by tidy
                 ... = ((F.map π_Θ) ⊚ (F.map ψ)) ∘ 𝔸.α      : by rw ←functor.map_comp
                 ... = (F.map π_Θ) ∘ ((F.map ψ) ∘ 𝔸.α)       : rfl
                 ... = (F.map π_Θ) ∘ (Β.α ∘ ψ)               : by rw ← hom_g,
        
        have h3 : _ := h.2 (F.obj Β_Θ) ((F.map π_Θ) ∘ Β.α) h2,

        let α : Β_Θ → F.obj Β_Θ := some h3,

        use α,

        exact some_spec h3

    end

theorem coeq_competitor  (ℚ : Coalgebra F) 
                    (q : homomorphism Β ℚ) 
                    (h : q ∘ ϕ = q ∘ ψ)
        : 
        let Β_Θ := theta ϕ ψ in
        let π_Θ := coequalizer ϕ ψ in
        let α := some (coequalizer_is_homomorphism ϕ ψ) in        
            ∃! χ : homomorphism ⟨Β_Θ , α⟩ ℚ ,
            χ ∘ π_Θ = q.val
    := 
    begin
        intros Β_Θ π_Θ α,
        have sub_ker : sub_kern π_Θ q := coequalizer_kern ϕ ψ ℚ q h,
        have hom_π : _ :=(some_spec (coequalizer_is_homomorphism ϕ ψ)).1,

        have diag : _ := coalgebra_diagram 
                    (⟨π_Θ, hom_π⟩: homomorphism Β ⟨Β_Θ , α⟩) 
                    q
                    (quot_is_surjective ϕ ψ),
        exact diag.2 sub_ker
    end

theorem set_coequalizer_is_coalgebra_coequalizer :
    let Β_Θ := theta ϕ ψ in
    let π_Θ : Β.carrier ⟶ Β_Θ := coequalizer ϕ ψ in
    let α : Β_Θ → F.obj (Β_Θ):=  some (coequalizer_is_homomorphism ϕ ψ) in
    let h_π := (some_spec (coequalizer_is_homomorphism ϕ ψ)).1 in
    let co_Β_Θ : Coalgebra F := ⟨Β_Θ, α⟩ in
    let π₁ : Β ⟶ co_Β_Θ := ⟨π_Θ, h_π⟩ in
    is_coequalizer
        ϕ ψ π₁ := 
    begin
        intros Β_Θ π_Θ α h_π co_Β_Θ π₁,
        let ϕ₁ : 𝔸.carrier ⟶ Β.carrier := ϕ.val,
        let ψ₁ : 𝔸.carrier ⟶ Β.carrier := ψ.val,
        split, 
        have h : is_coequalizer ϕ₁ ψ₁ π_Θ := quot_is_coequalizer ϕ ψ,
        have h1 : _ := h.1,
        exact eq_in_set.1 h1,
        intros ℚ q h,
        have h₁ : q.val ⊚ ϕ₁ = q.val ⊚ ψ₁ := eq_in_set.2 h,


        have com : ∃! χ : homomorphism ⟨Β_Θ , α⟩ ℚ ,
                         χ ∘ π_Θ = q.val := 
            begin
                have sub_ker : sub_kern π_Θ q := coequalizer_kern ϕ ψ ℚ q h₁,
                have hom_π : _ :=(some_spec (coequalizer_is_homomorphism ϕ ψ)).1,

                have diag : _ := coalgebra_diagram 
                            (⟨π_Θ, hom_π⟩: homomorphism Β ⟨Β_Θ , α⟩) 
                            q
                            (quot_is_surjective ϕ ψ),
                exact diag.2 sub_ker
            end,
        let χ : co_Β_Θ ⟶ ℚ := some com,
        use χ,
        have spec : χ ∘ π_Θ = q := (some_spec com).1,
        
        have h1 : (χ ⊚ π₁) = q := eq_in_set.1 spec,
        split,
        exact h1,
        intros χ₁ coeq,
        have coeq1 : χ₁ ⊚ π₁ = χ ⊚ π₁ := by simp[h1 , coeq],
        haveI ep : epi π_Θ := (epi_iff_surjective π_Θ).2 
                                (quot_is_surjective ϕ ψ),
        have coeq2 : χ₁.val ⊚ π_Θ = χ.val ⊚ π_Θ := 
                    eq_in_set.2 coeq1,
        
        have coeq3: χ₁.val = χ.val := right_cancel π_Θ coeq2,

        exact eq_in_set.1 coeq3,
    end



end coalgebra_coequalizer