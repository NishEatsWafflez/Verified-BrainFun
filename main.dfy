include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"
include "triviallemmas.dfy"
include "loops.dfy"
include "compilationhelper.dfy"


module BrainFun {
import opened Lemmas
import opened Common
import opened Steps
import opened Equivalence
import opened Trivial
import opened Loops
import opened CompilationHelper

method CreateFinalIR(p: Program, commands: seq<Instr>) returns (result: IntermediateRep)
requires valid_program(p) //Trivially proven
requires valid_loop_program(p)
requires valid_input(p.input) //Trivially proven
requires |commands| == |Changes(p)| //Not trivially proven
requires changes_correct(p, Changes(p)) //Already proven
requires valid_ir_commands(commands)
requires matched_forall_loop(p, commands, Changes(p), |commands|) //Not trivially proven yet
ensures valid_ir(result)
ensures aligned_instructions(p, result)
ensures valid_input(result.input)
ensures valid_loop_ir(result)
ensures FullEquivalence(p, result)

{
  result := IntermediateRep(commands, 0, p.input);
  AlignmentMeansEquivalenceAllStates(p, result);
  aligned_implies_valid(p, result);
  assert valid_input(result.input);
}



method ReplaceElementInInstr(p: Program, commands: seq<Instr>, indices: seq<int>, j: int, loop_stack: seq<int>) returns (result: seq<Instr>)
requires valid_program(p)
requires indices == Changes(p)
requires changes_correct(p, indices)
requires 0 <= j
requires 0 <= j+1 <= |indices|
requires 0 <= j+1 <= |commands|
requires |loop_stack| > 0
requires |commands| > 1
requires commands[|commands|-1] == Jump(0, false)
requires matched_forall_loop(p, commands, indices, j+1)

requires valid_ir_commands(commands)
requires loop_less_than_commands(loop_stack, commands)
ensures |result| == |commands|
ensures matched_forall_loop(p, result, indices, j+1)
ensures loop_less_than_commands(loop_stack, result)
ensures valid_ir_commands(result)
ensures matched_command_with_ir(p, result, j, indices)

{
  var index := loop_stack[|loop_stack|-1];
  assert index in loop_stack;
  assert 0 <= index < |commands|;
  var result1 := commands[..index] + [Jump(|commands|-1, true)] + commands[index+1..];
  ReplacingJumpWithJump(p, commands, result1, index, indices, j+1);
  result := result1[..|result1|-1] + [Jump(index, false)];
  ReplacingEndJumpWithJump(p, result1, result, |commands|-1, indices, j+1);
  assert matched_forall_loop(p, result, indices, j+1);
  assert loop_less_than_commands(loop_stack, result);
  MatchedForallImpliesMatchedOne(p, result, indices, j);
}


method Compile(p: Program)  returns (result: IntermediateRep)
  requires valid_program(p)
  requires |p.commands| > 0
  requires valid_loop_program(p)
  requires p.pointer == 0
  requires valid_input(p.input)
  
  ensures valid_ir(result)
  ensures valid_input(result.input)
  ensures valid_loop_ir(result)
  ensures FullEquivalence(p, result)
{
  var i: int := 0;
  var j: int := 0;

  var loop_start_stack: seq<int> := []; 
  var next_command_indices := Changes(p);
  ChangeLemma(p, next_command_indices);
  ForAllHelper(p, next_command_indices);
  assert changes_correct(p, next_command_indices);
  assert forall d:: 0 <= d < |next_command_indices| ==> 0<= next_command_indices[d] < |p.commands|;
  assert sub_changes(p, next_command_indices);
  assert sub_changes_1_step(p, next_command_indices);
  ForAllStep(p, next_command_indices);
  ForAllStep2(p, next_command_indices);
  assert sub_changes_inclusion(p, next_command_indices);
  assert sub_changes_inclusion_1_step(p, next_command_indices);
  var indices_of_i: seq<int> := [];
  assert i in next_command_indices;
  assert sub_changes_inclusion(p, next_command_indices);
  assert sub_changes_inclusion_1_step(p, next_command_indices);
  assert 0 in next_command_indices;
  assert 0 < |p.commands|;
  assert (0 < |p.commands| && 0 in next_command_indices);
  assert i == 0;
  assert (i < |p.commands| && i in next_command_indices);
  assert inside_the_indices(p, next_command_indices, i);
  var commands: seq<Instr> := [];
  assert j==0;
  assert next_command_indices[j]==i;
  assert !(j>0);
  interpret_changes_correct(p, next_command_indices);
  assert j>0 ==> matched_command_with_ir(p, commands, j-1, next_command_indices);
  while i < |p.commands|
    invariant i >= 0
    invariant |commands|>=0
    decreases |p.commands| - i
    invariant sub_changes_inclusion_1_step(p, next_command_indices)
    invariant inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    invariant forall k:: k in indices_of_i ==> k < |p.commands| && inside_the_indices(p, next_command_indices, i)
    invariant forall k:: k in indices_of_i ==> i>k && k in next_command_indices
    invariant forall k:: k in indices_of_i ==> k in next_command_indices
    invariant j < |next_command_indices| ==> next_command_indices[j]==i
    invariant i >= |p.commands| ==> !(i in next_command_indices)
    invariant i >= |p.commands| ==> j >= |next_command_indices|
    invariant j <= |next_command_indices| && indices_of_i == next_command_indices[..j]
    invariant !(i in indices_of_i)
    invariant j == |commands|
    invariant j == |indices_of_i|
    invariant matched_forall_loop(p, commands, next_command_indices, j)
    invariant in_bounds_commands(p, next_command_indices)
    invariant loop_less_than_commands(loop_start_stack, commands)
    invariant valid_ir_commands(commands)
  {
    assert valid_ir_commands(commands);
    assert loop_less_than_commands(loop_start_stack, commands);
    assert j == |indices_of_i|;
    assert j <= |next_command_indices| ==> indices_of_i == next_command_indices[..j];
    assert inside_the_indices(p, next_command_indices, i) && i < |p.commands| ==> i in next_command_indices;
    assert i < |p.commands|;
    assert inside_the_indices(p, next_command_indices, i) ==> i in next_command_indices;
    assert j < |next_command_indices| ==> next_command_indices[j]==i;
    var old_i := i;
    assert old_i == i;
    assert j < |next_command_indices| ==> next_command_indices[j]==old_i;
    assert old_i in next_command_indices;
    assert i < |p.commands|;
    AndElim(indices_of_i, i, next_command_indices);
    assert forall k:: k in indices_of_i ==> i> k;// && i!= k;
    assert j == |indices_of_i|;
    indices_of_i := indices_of_i + [i];
    assert indices_of_i[|indices_of_i|-1] == i;
    assert j == |indices_of_i|-1;
    assert indices_of_i[j] == i;
    assert |indices_of_i| == j+1;
    assert j < |next_command_indices| ==> next_command_indices[j]==i;
    assert j <= |next_command_indices| ==> indices_of_i[..j] == next_command_indices[..j];
 
    assert j < |next_command_indices| ==> indices_of_i[j] == next_command_indices[j];
    extension(j, indices_of_i, next_command_indices);
    assert j+1 <= |next_command_indices| ==> indices_of_i == next_command_indices[..j+1];
    assert forall k:: k in indices_of_i ==> k < |p.commands| && inside_the_indices(p, next_command_indices, i);
    assert forall k:: k in indices_of_i ==> k in next_command_indices;
    EquivStatement(indices_of_i, next_command_indices);
    assert forall k:: int_in_seq(k, indices_of_i) ==> int_in_seq(k, next_command_indices);
    assert next_command_indices[j]==i;
    {match p.commands[i]
    case '+' =>
      assert i >= 0;
      assert valid_program(p);
      assert next_command_indices == Changes(p);
      assert |p.commands| > 0;
      // assert |p.input| == |p.commands|;
      assert p.pointer == 0;
      assert valid_input(p.input);
      assert |commands|>=0;
      assert changes_correct(p, next_command_indices);
      assert sub_changes_inclusion_1_step(p, next_command_indices);
      assert inside_the_indices(p, next_command_indices, i); //i is either greater than |p.commands| or i is in the indices
      assert 0<=j < |next_command_indices|;
      assert j < |next_command_indices| ==> next_command_indices[j]==i;
      assert i >= |p.commands| ==> !(i in next_command_indices);
      assert i >= |p.commands| ==> j >= |next_command_indices|;
      assert j == |commands|;
      assert old_i == i;
      assert p.commands[next_command_indices[j]] == '+';
      assert matched_forall_loop(p, commands, next_command_indices, j);
      assert in_bounds_commands(p, next_command_indices);
      assert loop_less_than_commands(loop_start_stack, commands);
      assert valid_ir_commands(commands);    
      commands, i := CompilePlus(p, commands, i, next_command_indices, j, old_i, loop_start_stack);
    case '-' =>
        commands, i := CompileMinus(p, commands, i, next_command_indices, j, old_i, loop_start_stack);
    case '>' =>
        commands, i := CompileRightShift(p, commands, i, next_command_indices, j, old_i, loop_start_stack);

    case '<' =>
      commands, i := CompileLeftShift(p, commands, i, next_command_indices, j, old_i, loop_start_stack);

    case '.' | ',' =>        
      commands, i := CompileIO(p, commands, i, next_command_indices, j, old_i, loop_start_stack);  
  
    case '[' | ']' =>
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= 1;
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        single_step_within_range(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);
        assert |commands| >= 0;

            
        if p.commands[next_command_indices[j]] == '['{
          commands, i := CompileTrueJump(p, commands, i, next_command_indices, j, old_i, loop_start_stack);
          loop_start_stack := AddElementToStack(loop_start_stack, commands);
          assert loop_less_than_commands(loop_start_stack, commands);

        }  
        else {
          commands, i := CompileFalseJump(p, commands, i, next_command_indices, j, old_i, loop_start_stack);
          if |loop_start_stack| > 0{
            assert loop_less_than_commands(loop_start_stack, commands);
            assert |loop_start_stack| > 0;
            assert valid_program(p);
            assert next_command_indices == Changes(p);
            assert changes_correct(p, next_command_indices);
            assert 0 <= j+1 <= |next_command_indices|;
            assert 0 <= j+1 <= |commands|;
            assert |loop_start_stack| > 0;
            assert |commands| > 1;
            assert commands[|commands|-1] == Jump(0, false);
            assert matched_forall_loop(p, commands, next_command_indices, j+1);
            assert valid_ir_commands(commands);
            assert loop_less_than_commands(loop_start_stack, commands);
            commands := ReplaceElementInInstr(p, commands, next_command_indices, j, loop_start_stack);
            ShrinkingLoopStartStack(loop_start_stack, commands);
            loop_start_stack := loop_start_stack[..|loop_start_stack|-1];
            assert loop_less_than_commands(loop_start_stack, commands);
          }


        }
        assert matched_forall_loop(p, commands, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, commands);
        assert valid_ir_commands(commands);

    case _ => {assume{:axiom} false;}
    
    }
    assert valid_ir_commands(commands);
    assert loop_less_than_commands(loop_start_stack, commands);
    assert j== |commands|-1;
    assert matched_forall_loop(p, commands, next_command_indices, j+1);
    assert in_bounds_commands(p, next_command_indices);
    assert old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, i);
    assert inside_the_indices(p, next_command_indices, i);

    assert j < |next_command_indices| ==> indices_of_i[j] == next_command_indices[j];
    assert j+1 <= |next_command_indices| ==> j < |next_command_indices|;
    assert 1<= j+1 <= |next_command_indices| ==> indices_of_i[j] == next_command_indices[j];
    assert j+1 <= |next_command_indices| ==> indices_of_i == next_command_indices[..j+1];

    var k := j+1;


    addition_preserving_2(indices_of_i, next_command_indices, j, k);

    assert k >= 1;
    assert 1<= k <= |next_command_indices| ==> indices_of_i[k-1] == next_command_indices[k-1];
    addition_preserving_3(indices_of_i, next_command_indices, j, k);
    assert k <= |next_command_indices| ==> indices_of_i == next_command_indices[..k];

    assert matched_forall_loop(p, commands, next_command_indices, k);

    j := k;


    assert j <= |next_command_indices| ==> indices_of_i == next_command_indices[..j];
    assert 1<= j <= |next_command_indices| ==> indices_of_i[j-1] == next_command_indices[j-1];

    assert j == |commands|;
    assert |commands|-1 == j-1;
    assert j > 0;
    assert matched_forall_loop(p, commands, next_command_indices, j);


    assert i >= 0;
    assert |commands| >=0;
    assert sub_changes_inclusion_1_step(p, next_command_indices);

    assert inside_the_indices(p, next_command_indices, i);
    assert forall k:: k in indices_of_i ==> k < |p.commands| && inside_the_indices(p, next_command_indices, i);
    assert forall k:: k in indices_of_i ==> i>k && k in next_command_indices;
    greater_not_equal(indices_of_i, i);
    assert !(i in indices_of_i);

    assert j==|commands|;
    assert j == |indices_of_i|;
    assert j < |next_command_indices| ==> next_command_indices[j]==i;
    assert in_bounds_commands(p, next_command_indices); 
    in_bounds_commands_implies_not_in(p, next_command_indices, i);


  }
  length_constraints(j, indices_of_i, next_command_indices);
  assert |indices_of_i| == |commands|;
  assert |commands| == |next_command_indices|;
  result := CreateFinalIR(p, commands);
  return result;
}

method CompileFromString (commands: seq<char>, input: seq<char>) returns (p: Program)
requires valid_input(input)
requires (forall i:: (0<= i < |commands| ==> commands[i] in [',', '[', ']', '.', '+', '-', '>', '<']))
requires |commands| > 0
requires valid_loop_program_helper(commands, 0, 0)
requires valid_loop(commands)
ensures valid_program(p)
ensures valid_loop_program(p)
{
  p := Program(commands, 0, input);

}  

method IRtoString(ir: IntermediateRep)
{
  var i := 0;
  while i < |ir.commands|
  decreases |ir.commands|-i
  {

    {match ir.commands[i]
      case Inc(k) => {
        print i, ": Inc(", k, ")";
      }
      case Move(k) => {
        print i, ": Move(", k, ")";
      }
      case Print => {
        print i, ": Print";
      }
      case UserInput => {
        print i, ": UserInput";
      }
      case Jump(dest, dir) => {
        print i, ": Jump(", dest, ", ", dir, ")";
      }
    }
    if i == ir.pointer {
      print " <--";
    }
    print "\n";
    i := i+1;
  }
  print "User Input: ";
  i := 0;
  while i < |ir.input| {
    print ir.input[i];
    i := i+1;
  }
  print "\n";
}

}