// include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"


module Equivalence{
    // import opened Lemmas
    import opened Common
    import opened Steps
    ghost predicate AreEquivalent(bf_program: Program, bf_state: State, ir_program: IntermediateRep, input: seq<char>, inputPtr: int)
    requires 0 <= bf_program.pointer <= |bf_program.commands|
    requires 0 <= bf_state.pointer < |bf_state.memory| 
    decreases |bf_program.commands|- bf_program.pointer
    requires 0 <= inputPtr <= |input|
    requires valid_program(bf_program) 
    requires state_reqs(bf_state)
    ensures !(bf_program.pointer >= |bf_program.commands| && !(ir_program.pointer >= |ir_program.commands|)) || !(!(bf_program.pointer >= |bf_program.commands|) && (ir_program.pointer >= |ir_program.commands|))
        {
            if bf_program.pointer >= |bf_program.commands| && ir_program.pointer >= |ir_program.commands| then
                true
            else if !(bf_program.pointer >= |bf_program.commands| && !(ir_program.pointer >= |ir_program.commands|)) || !(!(bf_program.pointer >= |bf_program.commands|) && (ir_program.pointer >= |ir_program.commands|)) then
            // else 
                // exists i: int :: true
                // true
                exists next_bf_state: State, next_bf_program: Program, next_ir: IntermediateRep, postPtr: int:: 
                0<=bf_program.pointer < next_bf_program.pointer <= |next_bf_program.commands| &&
                0 <= ir_program.pointer < next_ir.pointer <= |ir_program.commands| &&
                inputPtr <= postPtr <= |input| &&

                next_ir.commands == ir_program.commands && bf_program.commands == next_bf_program.commands
                &&
                state_reqs(next_bf_state)
                &&
                |next_bf_state.memory| == |bf_state.memory|
                // &&
                && 0<=next_bf_state.pointer < |next_bf_state.memory| 
                && max_steps(bf_program, bf_state, next_bf_program, next_bf_state)
                && ir_step(ir_program, bf_state, next_ir, next_bf_state) && AreEquivalent(next_bf_program, next_bf_state, next_ir, input, postPtr)
            
            else
                false
        }


    ghost predicate EquivalentReps(p: Program, s: State, ir: IntermediateRep)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    {
        //Idea: forall values, from any linear location in the program or in the code, they should transition to the same spot
        // Will call this from any state as well
(        forall i:: within_ir_range(i, ir) ==> exists p': Program, s': State, ir': IntermediateRep, s1: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(s1) && valid_state(s, s1) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', s1) && s'==s1 )
    }

    ghost predicate lockstep(p: Program, s: State, ir: IntermediateRep)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input)
    {
        valid_program(p) && valid_ir(ir) && state_reqs(s) &&
        exists p': Program, s': State, ir': IntermediateRep ::
        valid_program(p') && state_reqs(s')&& valid_ir(ir')&& valid_input(ir'.input)&& valid_state(s, s')&& aligned_programs(p, p') &&
        max_steps( p, s, p', s') &&
        ir_step(ir, s, ir', s')     
    }

 
ghost predicate aligned_instructions(p: Program, ir: IntermediateRep)
    requires valid_program(p)
    requires valid_ir(ir)
    {
        (|Changes(p)| == |ir.commands|)
        && forall i:: 0<=i<|ir.commands| ==>(
            0<=Changes(p)[i] < |p.commands| &&
               match ir.commands[i]
                case Inc(k) => (p.commands[Changes(p)[i]] in ['+', '-'] && (k>= 0 ==> ((p.commands[Changes(p)[i]]=='+') && k==count_consecutive_symbols(p, Changes(p)[i]))) && (k<0 ==> (p.commands[Changes(p)[i]]=='-')&&(-k)==count_consecutive_symbols(p, Changes(p)[i]))
                )
                case Move(k) => 
                (p.commands[Changes(p)[i]] in ['>', '<'] && (k>= 0 ==> ((p.commands[Changes(p)[i]]=='>') && k==count_consecutive_symbols(p, Changes(p)[i]))) && (k<0 ==> (p.commands[Changes(p)[i]]=='<')&&(-k)==count_consecutive_symbols(p, Changes(p)[i])))
                case UserInput => p.commands[Changes(p)[i]] == ','
                case Print => p.commands[Changes(p)[i]] == '.'
                case Jump(dest, direction) => ((p.commands[Changes(p)[i]] == ']' && direction == false) || (p.commands[Changes(p)[i]] == '[' && direction == true))
        
        )
        // (p.pointer == |p.commands| && ir.pointer == |ir.commands|) ||
        // (p.pointer < |p.commands| && ir.pointer < |ir.commands| &&
        
        //  )
    } 

}

