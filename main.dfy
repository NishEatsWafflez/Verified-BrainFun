include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"


module BrainFun {
import opened Lemmas
import opened Common
import opened Steps
import opened Equivalence

//TODO: I need to define a predicate that takes a program, a state, and a post-state (maybe a post-program idk) 
// and says that that state will be reached when we've done the maximal amount of merge-able steps (this means that after doing ++-++--- we get to here, 
// requires that the next spot either be out of bounds or not a compatible character, prob semi-recursive idk) need to figure out how loops work with that,
// maybe if we see a begin loop, we run until we get to the end of the loop (recursively call the function on the internal thing)

// The main compile method, still need to verify that the result is correct :D
method Compile(p: Program)  returns (result: IntermediateRep)
  requires valid_program(p)
  requires |p.commands| > 0
  requires |p.input| == |p.commands|
  requires p.pointer == 0
  requires valid_input(p.input)
  // ensures AreEquivalent(p, InitialState(), result, input, 0)
  ensures |result.commands| > 0 && |p.commands| > 0
  // ensures EquivalentReps(p, InitialState(), result)

{
  var i: nat := 0;
  var j: int := 0;

  var loop_start_stack: seq<int> := []; // Stack to store indices of '['

  var commands: seq<Instr> := [];

  var next_command_indices := Changes(p);
  assert i < |p.commands|;
  while i < |p.commands|
    invariant |commands|>=0
    decreases |p.commands| - i
    invariant 0 < i ==> |commands| > 0
    invariant |loop_start_stack| > 0 ==> (0< loop_start_stack[|loop_start_stack|-1]+1  <= |commands|)
    invariant forall j:: 0<=j < |loop_start_stack|-1 ==> loop_start_stack[j]<loop_start_stack[j+1]
    invariant forall j:: 0<=j < |loop_start_stack| ==> |commands|>loop_start_stack[j] >= 0
    // invariant 0 < i ==> |commands| > 0 || wasMoving || wasIncrementing
    invariant 0 <= j < |p.input|
  {
    {match p.commands[i]
      case '+' =>
        var k:= count_consecutive_symbols(p, i);
        commands := commands+ [Inc(k)];
        i:= i+k-1; 
        assert |commands|>0;
      case '-' =>
        var k:= count_consecutive_symbols(p, i);
        var neg_k: int := k;
        commands := commands+ [Inc(-1*neg_k)];
        i:= i+k-1; 
        assert |commands|>0;
      case '>' =>
        var k:= count_consecutive_symbols(p, i);
        commands := commands+ [Move(k)];
        i:= i+k-1; 
                assert |commands|>0;
      case '<' =>
        var k:= count_consecutive_symbols(p, i);
        var neg_k: int := k;
        commands := commands+ [Move(-1*neg_k)];
        i:= i+k-1; 
                assert |commands|>0;
      case '.' =>
        commands := commands + [Print];
        assert |commands|>0;
      case ',' =>
        commands := commands + [UserInput];
                assert |commands|>0;
      case '[' =>
        assert |loop_start_stack| >= 0;
        assert (|loop_start_stack| > 1) ==> loop_start_stack[|loop_start_stack|-2] < loop_start_stack[|loop_start_stack|-1];
        loop_start_stack := loop_start_stack + [|commands|]; 
        assert |loop_start_stack| >= 1;
        assert loop_start_stack[|loop_start_stack|-1] == |commands|;
        assert |commands| >= 0;
        commands := commands + [Jump(0, true)]; 
        assert 0<= loop_start_stack[|loop_start_stack|-1] < |commands|;
        assert forall i:: 0<=i< |loop_start_stack| ==> 0<= loop_start_stack[i] < |commands|;
        assert |commands|>0;
      case ']' =>
        if |loop_start_stack| > 0 {

          var start_index := loop_start_stack[|loop_start_stack| - 1];
          assert start_index == loop_start_stack[|loop_start_stack|-1];
          assert (|loop_start_stack| > 1) ==> loop_start_stack[|loop_start_stack|-2] < loop_start_stack[|loop_start_stack|-1];

          loop_start_stack := loop_start_stack[0 .. |loop_start_stack| - 1];
          var loop_body := commands[start_index + 1 .. |commands|];
          assert |commands[0..start_index]| == start_index;
          commands := commands[0 .. start_index] + [Jump(|commands|, true)] + commands[start_index+1..] + [Jump(start_index,false)];
          assert (|loop_start_stack|>0) ==> loop_start_stack[|loop_start_stack|-1] < start_index;
          assert (|loop_start_stack|>0) ==> loop_start_stack[|loop_start_stack|-1] <start_index < |commands|;  
          assert (|loop_start_stack| > 0) ==> loop_start_stack[|loop_start_stack| - 1] < |commands|;
          assert forall i :: 1 <= i < |loop_start_stack| ==> loop_start_stack[i - 1] < loop_start_stack[i] ;
          if (|loop_start_stack| > 0) {
              LemmaStrictlyIncreasing(loop_start_stack);
              AllLessThanLast(loop_start_stack); 
              assert forall i :: 0 <= i < |loop_start_stack| ==> loop_start_stack[i] <= loop_start_stack[|loop_start_stack|-1];
          } else{
              assert forall i :: 0 <= i < |loop_start_stack|==> loop_start_stack[i] < loop_start_stack[|loop_start_stack|-1]; 
          }


          assert |loop_start_stack| > 0 ==> 0 < loop_start_stack[|loop_start_stack|-1]+1;


        assert |commands|>0;
        } 
    }
    assert |commands|>0;
    i := i + 1;

  }

  assert |commands| > 0;    
  var compiled_ir := IntermediateRep(commands, 0, p.input);
  // ExistsAdvancedIntermediate(compiled_ir);
  // ExistsAdvancedProgram(p);

  // assert exists ir': IntermediateRep :: 
  //           ir'.commands == compiled_ir.commands &&
  //           0 <= compiled_ir.pointer < ir'.pointer <= |compiled_ir.commands|;
  // assert exists p': Program ::valid_program(p');
  // assert state_reqs(InitialState());
  // assert exists s': State :: state_reqs(s');
  var s:= InitialState();
  MaxSteps(p, s);
  // assert exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s');
  IrStep(compiled_ir, s);
  // MaxKSteps(p, s, 1); 
  // forall k | 0 <= k {
  //   MaxKSteps(p, s, k);
  // }
  // forall k | 0 <= k {
  //   MaxKIRSteps(compiled_ir, s, k);
  // }  
  // // assert forall k:: 0<=k ==> (exists ir': IntermediateRep, s': State ::  
  // //   valid_ir(ir') && state_reqs(s')&& valid_ir(ir')&& valid_input(ir'.input) && 
  // //   ir_k_steps(compiled_ir, s, ir', s', k) );  
  // // assert forall k:: 0<=k ==> (exists p': Program, s': State ::  
  // //   valid_program(p') && state_reqs(s') && 
  // //   program_k_max_steps(p, s, p', s', k));
  // //   CombineForAlls(p, s, compiled_ir);
  
  // assert StepsForBoth(p, s, compiled_ir);
  assume aligned_instructions(p, compiled_ir); // TODO: prove this
  AlignmentMeansEquivalence(p, s, compiled_ir);

  return compiled_ir;
  // return null;
}
  method Main()
    ensures true  
  {
    print "Hello, World!\n";
  }

}
