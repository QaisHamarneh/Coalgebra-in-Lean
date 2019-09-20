import examples.automata



namespace Automata

    variables {Sigma : Type}       -- The alphabet
              {D : Type}            -- Output
    open word 

    structure Automaton    :=         
            (State : Type)                 -- Set of States
            (δ : State → Sigma → State)    -- δ: S × Σ → S
            (γ : State → D)                -- Output of a state

    /-
    Given a morphism τ between two Automates A and B
    determines if τ is a homomorphism
    -/

    def is_homomorphism_Automaton                
        {A B : @Automaton Sigma D} (τ : A.State → B.State) : Prop :=   
            ∀ a : A.State ,                     -- ∀ states (a) in A
                A.γ a  = B.γ (τ a) ∧            -- a ∈ T_A iff τ(a) ∈ T_B
            ∀ e : Sigma ,                       -- and ∀ e ∈ Σ
                τ (A.δ a e) = (B.δ (τ a) e)     -- τ(δ_A(a , e)) = δ_B(τ(a) , e)


    def deltaStar {A : @Automaton Sigma D} (s : A.State): word Sigma → A.State 
        | ε           :=  s 
        | (e•v)       :=  A.δ (deltaStar v) e


    def state_output 
        {A : Automaton} 
        (s : A.State) 
        (w : @word Sigma) : D :=
        A.γ (deltaStar s w)


    

    inductive T_tree : Type 
        | node : D → (Sigma → T_tree) → T_tree

    notation  d ` - ` φ  := T_tree.node d φ

    def delta : @T_tree Sigma D → Sigma → @T_tree Sigma D
        | (d - φ) e := φ e

    def gamma : @T_tree Sigma D → D
        | (d - φ) := d

    def Tree_Automaton : Automaton :=
    {
        State       := @T_tree Sigma D,
        δ           := delta ,
        γ           := gamma
    }

    def Terminal_Automaton : Automaton :=
    {
        State       := word Sigma → D ,
        δ           := λ τ e , λ w , τ (e • w)  , 
        γ           := λ τ , τ word.ε
    }


    def φ (A : @Automaton Sigma D) : 
          A.State → (@Terminal_Automaton Sigma D).State
        | a word.ε      := A.γ a
        | a (e • w)     := φ (A.δ a e) w

    theorem Terminal_is_Automaton (A : @Automaton Sigma D) :
            is_homomorphism_Automaton (φ A) := 
            assume a : A.State , 
            and.intro
                begin
                    apply rfl,
                end
                begin
                    intro e,
                    apply rfl
                end

end Automata







