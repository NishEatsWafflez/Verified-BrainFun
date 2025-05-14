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
  requires |p.input| == |p.commands|
  requires p.pointer == 0
  requires valid_input(p.input)
  // ensures AreEquivalent(p, InitialState(), result, input, 0)
  ensures |result.commands| > 0 && |p.commands| > 0
  ensures EquivalentReps(p, InitialState(), result)

{
  var i: nat := 0;
  var j: int := 0;
  var wasIncrementing: bool := false;
  var wasMoving:bool := false;
  var count: int := 0;
  var loop_start_stack: seq<int> := []; // Stack to store indices of '['

  var commands: seq<Instr> := [];
  while i < |p.commands|
    decreases |p.commands| - i
    invariant |loop_start_stack| > 0 ==> (0< loop_start_stack[|loop_start_stack|-1]+1  <= |commands|)
    invariant forall j:: 0<=j < |loop_start_stack|-1 ==> loop_start_stack[j]<loop_start_stack[j+1]
    invariant forall j:: 0<=j < |loop_start_stack| ==> |commands|>loop_start_stack[j] >= 0
    invariant 0 < i ==> |commands| > 0 || wasMoving || wasIncrementing
    invariant 0 <= j < |p.input|
  {
    {match p.commands[i]
      case '+' =>
        if wasMoving { 
          commands := commands + [Move(count)];
          count := 0;

        }else if wasIncrementing{
          count := count +1;
        }
        wasMoving := false;
        wasIncrementing := true;
        count := count + 1;
      case '-' =>
        if wasMoving { 
          commands := commands + [Move(count)];
          count := 0;

        }else if wasIncrementing{
          count := count -1;
        }
        wasMoving := false;
        wasIncrementing := true;
        count := count + 1;
      case '>' =>
        if wasIncrementing { 
          commands := commands + [Inc(count)];
          count := 0;
        }else if wasMoving{
          count := count +1;
        }
        wasMoving := true;
        wasIncrementing := false;
        commands := commands + [Move(1)];
      case '<' =>
        if wasIncrementing { 
          commands := commands + [Inc(count)];
          count := 0;

        }else if wasMoving{
          count := count -1;
        }
        wasMoving := true;
        wasIncrementing := false;
        commands := commands + [Move(-1)];
      case '.' =>
        if wasIncrementing { 
          commands := commands + [Inc(count)];
        } else if wasMoving {
          commands := commands + [Move(count)];
        }
        count := 0;
        wasIncrementing := false;
        wasMoving := false;

        commands := commands + [Print];
      case ',' =>
        if wasIncrementing { 
          commands := commands + [Inc(count)];
        } else if wasMoving {
          commands := commands + [Move(count)];
        }
        count := 0;
        wasIncrementing := false;
        wasMoving := false;
        assert j < |p.input|;
        commands := commands + [UserInput];
        if j == |p.input|-1{
          j := 0;
        }else{
          j := j+1;
        }
        assert j <= |p.input|;
      case '[' =>
        if wasIncrementing { 
          commands := commands + [Inc(count)];
        } else if wasMoving {
          commands := commands + [Move(count)];
        }
        count := 0;
        wasIncrementing := false;
        wasMoving := false;
        assert |loop_start_stack| >= 0;
        assert (|loop_start_stack| > 1) ==> loop_start_stack[|loop_start_stack|-2] < loop_start_stack[|loop_start_stack|-1];
        loop_start_stack := loop_start_stack + [|commands|]; 
        assert |loop_start_stack| >= 1;
        assert loop_start_stack[|loop_start_stack|-1] == |commands|;
        assert |commands| >= 0;
        commands := commands + [Jump(0, true)]; 
        assert 0<= loop_start_stack[|loop_start_stack|-1] < |commands|;
        assert forall i:: 0<=i< |loop_start_stack| ==> 0<= loop_start_stack[i] < |commands|;

      case ']' =>

        if wasIncrementing { 
          commands := commands + [Inc(count)];
        } else if wasMoving {
          commands := commands + [Move(count)];
        }
        count := 0;
        wasIncrementing := false;
        wasMoving := false;
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



        } 
      case _ =>
        print "error";}
    i := i + 1;
  }
  if wasIncrementing { 
      commands := commands + [Inc(count)];
  } else if wasMoving {
    commands := commands + [Move(count)];
  }
  assert |p.commands| > 0 ==> |commands| > 0;    
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
  MaxKSteps(p, s, 1); 
  forall k | 0 <= k {
    MaxKSteps(p, s, k);
  }
  forall k | 0 <= k {
    MaxKIRSteps(compiled_ir, s, k);
  }
  assert forall k:: 0<=k ==> (exists ir': IntermediateRep, s': State ::  
    valid_ir(ir') && state_reqs(s')&& valid_input(ir'.input) && 
    ir_k_steps(compiled_ir, s, ir', s', k) );  
  assert forall k:: 0<=k ==> (exists p': Program, s': State ::  
    valid_program(p') && state_reqs(s') && 
    program_k_max_steps(p, s, p', s', k));

  assert EquivalentReps(p, s, compiled_ir); 
  return compiled_ir;
  // return null;
}
  method Main()
    ensures true  
  {
    print "Hello, World!\n";
  }

}
