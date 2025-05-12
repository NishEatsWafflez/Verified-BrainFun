include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"


module Equivalence{
    import opened Lemmas
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
    {
        // true
        //Idea: forall i:: 0 <= i < |ir| ==> if program can transition from i to i+1, then ir can as well
        forall i:: 0 <= i < |ir.commands| ==> exists p': Program, s': State, ir': IntermediateRep:: valid_program(p') && state_reqs(s') && program_k_max_steps(p, s, p', s', i) && ir_k_steps(ir, s, ir', s', i)
    }
}

