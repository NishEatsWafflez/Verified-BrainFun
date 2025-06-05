// include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"


module Equivalence{
    // import opened Lemmas
    import opened Common
    import opened Steps
    // ghost predicate AreEquivalent(bf_program: Program, bf_state: State, ir_program: IntermediateRep, input: seq<char>, inputPtr: int)
    // requires 0 <= bf_program.pointer <= |bf_program.commands|
    // requires 0 <= bf_state.pointer < |bf_state.memory| 
    // decreases |bf_program.commands|- bf_program.pointer
    // requires 0 <= inputPtr <= |input|
    // requires valid_program(bf_program) 
    // requires state_reqs(bf_state)
    // ensures !(bf_program.pointer >= |bf_program.commands| && !(ir_program.pointer >= |ir_program.commands|)) || !(!(bf_program.pointer >= |bf_program.commands|) && (ir_program.pointer >= |ir_program.commands|))
    //     {
    //         if bf_program.pointer >= |bf_program.commands| && ir_program.pointer >= |ir_program.commands| then
    //             true
    //         else if !(bf_program.pointer >= |bf_program.commands| && !(ir_program.pointer >= |ir_program.commands|)) || !(!(bf_program.pointer >= |bf_program.commands|) && (ir_program.pointer >= |ir_program.commands|)) then
    //         // else 
    //             // exists i: int :: true
    //             // true
    //             exists next_bf_state: State, next_bf_program: Program, next_ir: IntermediateRep, postPtr: int:: 
    //             0<=bf_program.pointer < next_bf_program.pointer <= |next_bf_program.commands| &&
    //             0 <= ir_program.pointer < next_ir.pointer <= |ir_program.commands| &&
    //             inputPtr <= postPtr <= |input| &&

    //             next_ir.commands == ir_program.commands && bf_program.commands == next_bf_program.commands
    //             &&
    //             state_reqs(next_bf_state)
    //             &&
    //             |next_bf_state.memory| == |bf_state.memory|
    //             // &&
    //             && 0<=next_bf_state.pointer < |next_bf_state.memory| 
    //             && max_steps(bf_program, bf_state, next_bf_program, next_bf_state)
    //             && ir_step(ir_program, bf_state, next_ir, next_bf_state) && AreEquivalent(next_bf_program, next_bf_state, next_ir, input, postPtr)
            
    //         else
    //             false 
    //     }

    ghost predicate equiv_locations(p: Program, ir: IntermediateRep)
    {
        (ir.pointer == |ir.commands| && p.pointer == |p.commands|) || (0<= ir.pointer < |Changes(p)| && p.pointer == Changes(p)[ir.pointer])
    }
    ghost predicate EquivalentReps(p: Program, s: State, ir: IntermediateRep)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    {
        //For all values, from any linear location in the program or in the code, 
        //they should transition to the same spot
        (forall i:: within_ir_range(i, ir) ==> exists p': Program, s': State, ir': IntermediateRep, s1: State:: 
        valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && 
        program_k_max_steps(p, s, p', s', i) 
        && state_reqs(s1) && valid_state(s, s1) && valid_ir(ir') && valid_input(ir'.input) && 
        ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', s1) 
        && s'==s1)
    }

    ghost predicate FullEquivalence(p: Program, ir: IntermediateRep)
    requires valid_program(p)
    requires valid_ir(ir)
    requires valid_input(ir.input)
    {
        forall s: State:: state_reqs(s) ==> EquivalentReps(p, s, ir)
    }


ghost predicate matched_forall_loop(p: Program, ir: seq<Instr>, changes: seq<int>, bound: int)
requires valid_program(p)
requires changes == Changes(p)
requires 0<= bound <= |changes|
requires 0<= bound <= |ir|
requires forall k:: 0<= k < |changes| ==> 0<= changes[k] < |p.commands|
{
    forall k:: within_bounds(k, bound) ==> matched_command_with_ir(p, ir, k, changes)
}
ghost predicate within_bounds(k: int, b: int){
    0<=k<b
}

ghost predicate matched_command_with_ir(p: Program, ir: seq<Instr>, index: int, changes: seq<int>)
requires valid_program(p)
requires changes == Changes(p)
requires 0<= index < |changes|
requires 0<= index < |ir|
requires 0<= changes[index] < |p.commands|
{
match ir[index]
    case Inc(k) => 
    ((k>= 0 ==> ((p.commands[changes[index]]=='+') && k==count_consecutive_symbols(p, changes[index]))) && (k<0 ==> (p.commands[changes[index]]=='-')&&(-k)==count_consecutive_symbols(p, changes[index])))
    case Move(k) => 
        ((k>= 0 ==> ((p.commands[changes[index]]=='>') && k==count_consecutive_symbols(p, changes[index]))) && (k<0 ==> (p.commands[changes[index]]=='<')&&(-k)==count_consecutive_symbols(p, changes[index])))
    case UserInput => p.commands[changes[index]] == ','
    case Print => p.commands[changes[index]] == '.'
    case Jump(dest, false) => (
        (p.commands[changes[index]] == ']')
        // && p.commands[changes[dest]] == '[' && ir[dest] == Jump(index, true))
        // && valid_loop(p.commands[changes[dest]+1.. changes[index]])
        )
    case Jump(dest, true)=>
         (
            p.commands[changes[index]] == '['
            
            )
            
    
}

ghost predicate aligned_instructions_subseq(p: Program, ir: seq<Instr>)
    // requires forall i:: 0 <= i < |p.commands| ==> 0<= Changes(p)[i] < |p.commands|
    requires valid_program(p)
    // requires valid_ir(ir)
    {
        (|Changes(p)| >= |ir|)
        && forall i:: 0<=i<|ir| ==>(
            0<=Changes(p)[i] < |p.commands| &&
            matched_command_with_ir(p, ir, i, Changes(p))
        )
        // (p.pointer == |p.commands| && ir.pointer == |ir.commands|) ||
        // (p.pointer < |p.commands| && ir.pointer < |ir.commands| &&
        
        //  )
    } 


ghost predicate aligned_instructions(p: Program, ir: IntermediateRep)
    // requires forall i:: 0 <= i < |p.commands| ==> 0<= Changes(p)[i] < |p.commands|
    requires valid_program(p)
    requires valid_ir(ir)
    {
        (|Changes(p)| == |ir.commands|)
        && forall i:: 0<=i<|ir.commands| ==>(
            0<=Changes(p)[i] < |p.commands| &&
            matched_command_with_ir(p, ir.commands, i, Changes(p))
        )
        // (p.pointer == |p.commands| && ir.pointer == |ir.commands|) ||
        // (p.pointer < |p.commands| && ir.pointer < |ir.commands| &&
        
        //  )
    } 

}

