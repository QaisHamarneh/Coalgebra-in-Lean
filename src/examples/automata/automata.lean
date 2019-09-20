import data.set
open set


universes u₁ u₂ u₃ 

inductive word (Sigma : Type u₂)
        | ε  {}         : word
        | nonempty      : Sigma → word → word 




notation e ` • ` v := word.nonempty e v

notation `[[` l:(foldr `.` (e v, word.nonempty e v) word.ε) `]]` := l



section Automata_DFA 
    parameter {Sigma : Type u₂}             -- The alphabet
    open word


    structure DFA    :=         
            (State : Type u₁)                    -- Set of States
            (δ : State → Sigma → State)             -- δ: S × Σ → S
            (terminal: set State)               -- T ⊆ S
            (s₀ : State)                        -- S₀ the starting state

    /--
    Given a morphism τ between two Automates A and B
    determines if τ is a homomorphism
    -/
    def is_homomorphism                
        (A B : DFA) (τ : A.State → B.State) : Prop :=   
            ∀ a : A.State ,                                 -- ∀ states (a) in A
                a ∈ A.terminal ↔ τ a ∈ B.terminal ∧     -- a ∈ T_A iff τ(a) ∈ T_B
                    ∀ e : Sigma ,                       -- and ∀ e ∈ Σ
                        τ (A.δ a e) = (B.δ (τ a) e)     -- τ(δ_A(a , e)) = δ_B(τ(a) , e)


    def deltaStarDFA {A : DFA} (s : A.State): word Sigma → A.State 
        | ε           :=  s 
        | (e•v)       :=  A.δ (deltaStarDFA v) e


    def acceptedDFA (A : DFA) (w : word Sigma) : Prop :=
        @deltaStarDFA A A.s₀ w ∈ A.terminal

end Automata_DFA




section Automata_NFA
    parameter {Sigma : Type}
    open word

    structure NFA := mk::
            (State : Type)
            (δ : State → Sigma → set State)
            (terminal: set State)
            (s₀ : State) 


    variable N : NFA

    def deltaStarNFA {N :NFA} (s :N.State) : word Sigma→ set N.State 
        |ε         :=  {s}
        |(e•v)     :=  ⋃ s ∈ (deltaStarNFA v) ,
                                (N.δ s e)

    def acceptedNFA {N:NFA} (w : word Sigma) : Prop :=
        deltaStarNFA N.s₀ w ∩ N.terminal ≠ ∅

end Automata_NFA
    
    
    





section NFA_to_DFA
    parameters {Sigma:Type} (N : @NFA Sigma)

    open word

    open DFA
    open NFA

    def NFA_to_DFA: DFA := 
        {   
            State       :=  set N.State,
            δ       :=  λ(S : set N.State) (a : Sigma), 
                        ⋃ s ∈ S, (N.δ s a),
            terminal:=  {T: set N.State | T ∩ N.terminal ≠ ∅},
            s₀      :=  {N.s₀}
        }

    



    theorem same_language: 
        ∀ (word: word Sigma) ,
            deltaStarNFA N.s₀ word 
            = 
            deltaStarDFA 
                        NFA_to_DFA.s₀  
                        word 
        :=
        begin
            intro word,
            induction word,
            case word.ε : 
                {exact rfl},
            case word.nonempty  : 
                {   
                let e  := word_a,       --first letter
                let v  := word_a_1,     --rest of the word
                
                let NFA_reachable_with_v : set N.State := 
                        deltaStarNFA N.s₀ v,

                let DFA_reachable_with_v : set N.State := 
                        deltaStarDFA 
                            NFA_to_DFA.s₀
                            v,

                let NFA_reachable_with_word := deltaStarNFA N.s₀ 
                                    (e•v) ,

                let DFA_reachable_with_word := 
                    NFA_to_DFA.δ
                        DFA_reachable_with_v
                        e,

                have ih : NFA_reachable_with_v = DFA_reachable_with_v 
                                := word_ih,

                have h1 : NFA_reachable_with_word = 
                            ⋃ s ∈ NFA_reachable_with_v ,
                            (N.δ s e) := rfl,

                have h2 : DFA_reachable_with_word =
                            ⋃ s ∈ DFA_reachable_with_v, 
                            (N.δ s e) := rfl ,

                show 
                    NFA_reachable_with_word = DFA_reachable_with_word
                        , 
                from 
                    by {
                        rw [h1, ih] ,
                        apply rfl
                    }

                }
        end




end NFA_to_DFA




def D : DFA := 
{
    State           := ℕ,
    δ           := λ n (c : char) , n+1,
    terminal    := {2,3},
    s₀          := 0 
}

def w1 : word char := [['a' . 'b' . 'c']]

#reduce @deltaStarDFA char D (0:nat) w1

#reduce acceptedDFA D w1


