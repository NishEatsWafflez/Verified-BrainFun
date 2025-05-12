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




// ghost predicate equiv_representations(p: Program, ir: IntermediateRep, input: seq<char>)
// requires 0 == p.pointer < |p.commands|
// requires 0 == ir.pointer < |ir.commands|
// {
//       assert ir.pointer == 0;
//        ExistsAdvancedIntermediate(ir);
//       // AreEquivalent(p, InitialState(), ir, input, 0)

//     // s' := StateValue(new char[3000], 0);
//     // forall s: State:: 0 <= s.pointer < |s.memory| ==> AreEquivalent(p, s, ir)
// }

// ghost predicate program_k_max_steps(p: Program, s: State, p': Program, s': State, input: seq<char>, inputPtr: int, postPtr: int, k: int)
// decreases k
// requires 0<= k
// requires valid_program(p)
// requires 0<=inputPtr <= |input|
// {
//   if k==0 then
//     p == p' && s == s' && inputPtr == postPtr
//   else 
//     exists p'': Program, s'': State, midPtr: int:: valid_state(s, s'') && aligned_programs(p, p'') && max_steps(p, s, p'', s'') && inputPtr <= midPtr <= |input|&&
//     p.pointer < |p.commands| &&
//     program_k_max_steps(p'', s'', p', s', input, midPtr, postPtr, k-1)
// }
// ghost predicate Equivalence(p: Program, ir: IntermediateRep, input: seq<char>)
// requires valid_program(p)
// {
//   var s := InitialState();
//   var inputPtr := 0;
//   forall i:: 0 <= i < |ir.commands| ==> (exists s': State, p': Program, ir': IntermediateRep, postPtr: int:: 
//     program_k_max_steps(p, s, p', s', input, inputPtr, postPtr, i)
//   )
// }



method Compile(p: Program, input: seq<char>)  returns (result: IntermediateRep)
  requires valid_program(p)
  requires |input| == |p.commands|
  requires p.pointer == 0
  // ensures AreEquivalent(p, InitialState(), result, input, 0)
  ensures |result.commands| > 0 && |p.commands| > 0
  // ensures equiv_representations(p, result)
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
    invariant 0 <= j < |input|
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
        assert j < |input|;
        commands := commands + [UserInput(input[j])];
        if j == |input|-1{
          j := 0;
        }else{
          j := j+1;
        }
        assert j <= |input|;
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
        commands := commands + [Loop(IntermediateRep([], 0))]; 
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
          commands := commands[0 .. start_index] + [Loop(IntermediateRep(loop_body, 0))];
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
  var compiled_ir := IntermediateRep(commands, 0);
  ExistsAdvancedIntermediate(compiled_ir);
  ExistsAdvancedProgram(p);

  assert exists ir': IntermediateRep :: 
            ir'.commands == compiled_ir.commands &&
            0 <= compiled_ir.pointer < ir'.pointer <= |compiled_ir.commands|;

  // assert AreEquivalent(p, InitialState(), compiled_ir, input);
  return compiled_ir;
  // return null;
}
  method Main()
    ensures true  
  {
    print "Hello, World!\n";
  }

}
