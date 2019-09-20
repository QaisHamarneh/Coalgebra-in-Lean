import set_category.diagram_lemmas
import set_category.category_set
import set_category.limits.Equalizer
import help_functions
import coalgebra.Coalgebra
import coalgebra.subcoalgebra



import tactic.tidy

universes u



namespace coalgebra_equalizer

open category_theory 
     set 
     coalgebra
     classical
     function
     help_functions
     Equalizer
     coalgebra.Coalgebra
     category_set
     subcoalgebra
     

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

variables   {F : Type u ⥤ Type u}
            {𝔸 Β: Coalgebra F}
            (ϕ ψ : 𝔸 ⟶ Β)

theorem largest_subcoalgebra_equalizer 
    {C : set (equalizer_set ϕ ψ)}
    (lar : is_largest_coalgebra C):
    let E := equalizer_set ϕ ψ in
    let e : E → 𝔸 := (E ↪ 𝔸) in
    let ℂ : Coalgebra F := ⟨C , some lar.1⟩  in
    let σ : ℂ ⟶ 𝔸 := ⟨(e ∘ (C ↪ E))  , some_spec lar.1⟩ in
    is_equalizer ϕ ψ σ := 
    begin 
        intros E e ℂ σ,

        split,

        exact eq_in_set.1 
            (funext (λ c, ((C ↪ E) c).property)),
        
        intros Q q ϕq_ψq,

        have is_eq := (eqaulizer_set_is_equalizer ϕ ψ).2 q 
                    (eq_in_set.2 ϕq_ψq),

        let f : Q → E := some is_eq,
        have eq_f := some_spec is_eq,

        have fact : q.val = e ∘ f := eq_f.1,

        let f₁ : Q → (range f) := range_factorization f,

        let e₁ : range f → 𝔸 := e ∘ (range f ↪ E),

        have inj_e₁ : injective e₁ := 
            begin
                intros a₁ a₂ k,
                have inj_e : ∀ r₁ r₂, e r₁ = e r₂ → r₁ = r₂ := 
                    inj_inclusion 𝔸 E,
                have ra : (range f ↪ E) a₁ = (range f ↪ E) a₂ :=
                    inj_e a₁ a₂ k,
                have inj_r : ∀ q₁ q₂, 
                    (range f ↪ E) q₁ = (range f ↪ E) q₂ → q₁ = q₂ := 
                        inj_inclusion E (range f),
                exact (inj_r) a₁ a₂ ra,
            end,

        have inj_σ : injective σ := 
            begin
                intros a₁ a₂ k,
                have inj_e : ∀ r₁ r₂, e r₁ = e r₂ → r₁ = r₂ := 
                    inj_inclusion 𝔸 E,
                have ra : (C ↪ E) a₁ = (C ↪ E) a₂ :=
                    inj_e a₁ a₂ k,
                have inj_r : ∀ q₁ q₂, (C ↪ E) q₁ = (C ↪ E) q₂ → q₁ = q₂ := 
                    inj_inclusion E C,
                exact inj_r a₁ a₂ ra,
            end,

        have ex := Factorization q f₁ e₁ fact
            ((epi_iff_surjective f₁).2 surjective_onto_range) inj_e₁,

        let α_ℝ : range f → F.obj (range f) := some ex,

        have Rf_C : range f ⊆ C := 
            lar.2 (range f) (exists.intro α_ℝ (some_spec ex).1.2),

        let fc : Q.carrier → ℂ.carrier := λ q₁ , ⟨f q₁, Rf_C (f₁ q₁).property ⟩, 

        have f_fc : ∀ q₁, f q₁ = fc q₁ := λ q₁, rfl,

        have q_fc_σ_el : ∀ q₁ , q.val q₁ = (σ ∘ fc) q₁ := 
            λ q₁, 
            have s0 : (σ ∘ fc) q₁ = (e ∘ f) q₁ := rfl,
            by rw [fact, s0],
        
        have q_fc_σ : q.val = σ ∘ fc := funext q_fc_σ_el,
        
        have hom_σ_fc : @is_coalgebra_homomorphism F Q 𝔸 (σ ∘ fc) :=
            q_fc_σ ▸ q.property,

        have hom_fc : @is_coalgebra_homomorphism F Q ℂ fc :=
            inj_to_hom fc σ hom_σ_fc σ.property inj_σ,
        
        let h_fc : Q ⟶ ℂ := ⟨fc , hom_fc ⟩,

        use h_fc, 
        have s1 : q.val = (σ ⊚ h_fc).val := q_fc_σ,
        split,
        exact eq_in_set.1 s1,

        intros g q_σ_g,

        let σ₁ : ℂ.carrier ⟶ 𝔸.carrier := σ.val,

        have inj_σ₁ : injective σ₁ := inj_σ,

        haveI mo : mono σ₁ := (mono_iff_injective σ).2 inj_σ₁, 

        have s2 : (σ ⊚ g).val = (σ ⊚ h_fc).val := 
             q_σ_g ▸ s1,

        have s3 : σ.val ∘ g.val = σ.val ∘ h_fc.val := 
             s2,
        
        have s4 : g.val = h_fc.val :=  left_cancel σ₁ s3,

        exact eq_in_set.1 s4

    end

    


























end coalgebra_equalizer