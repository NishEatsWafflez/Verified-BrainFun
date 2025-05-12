include "common.dfy"
module Lemmas{
    import opened Common
// lemma MaxStepsPlusMinus(p: Program, s: State)
//   requires 0 <= p.pointer < |p.commands|
//   requires valid_program(p)
//   requires p.commands[p.pointer] in ['+', '-']
//   requires 0 <= s.pointer < |s.memory|
//   ensures exists p': Program, s': State :: p.commands == p'.commands && |s.memory| == |s'.memory| && 0 <= s'.pointer < |s'.memory|
//   && 0<= p'.pointer <= |p.commands| && max_steps(p, s, p', s') 
// {
//   var p' := Program(p.commands, p.pointer + 1, p.input);
//   assert p'.commands == p.commands;
//   var s' := StateValue(s.pointer, s.memory, s.output);
//   var count := 1;
//   assert p.commands[p.pointer] == '+' || p.commands[p.pointer] == '-';
//   // assert p'.pointer == p.pointer + 1;
//   assert forall i:: p.pointer <= i < p'.pointer ==> i == p.pointer;
//   assert forall i:: p.pointer <= i < p'.pointer ==> (p.commands[i] == p.commands[p.pointer] );
//   assert forall i:: p.pointer <= i < p'.pointer ==> (p.commands[i] == '+' || p.commands[i] == '-');
//   while p'.pointer < |p.commands| && p.commands[p'.pointer] in ['+', '-']
//     decreases |p.commands| - p'.pointer
//     invariant p'.commands == p.commands
//     invariant p'.pointer-1 < |p.commands|
//     invariant forall i:: i < p'.pointer ==> i < |p.commands|
//     invariant forall i:: p.pointer <= i < p'.pointer ==> (p.commands[i] == '+' || p.commands[i] == '-')
//   {
//     assert p.commands[p'.pointer] == '+' || p.commands[p'.pointer] == '-';
//     assert forall i:: p.pointer <= i < p'.pointer ==> (p.commands[i] == '+' || p.commands[i] == '-');
//     assert forall i:: p.pointer <= i <= p'.pointer ==> (p.commands[i] == '+' || p.commands[i] == '-');

//     p' := Program(p'.commands, p'.pointer + 1);
//     assert forall i:: p.pointer <= i < p'.pointer ==> (p.commands[i] == '+' || p.commands[i] == '-');
//     count := count + 1;
//     assert p.commands[p'.pointer-1] == '+' || p.commands[p'.pointer-1] == '-';
//     // assert forall i:: p.pointer <= i < 
//   }
//   assert p'.pointer == |p.commands| || (p'.pointer < |p.commands| && !(p.commands[p'.pointer] in['+', '-']));
//   assert p'.commands == p.commands;

//   var memory := s.memory;
//   memory := memory[s.pointer := memory[s.pointer] + count_commands(p, p', ['+', '-'])];
//   assert |memory| == |s.memory|;
//   var s'' := StateValue(s.pointer, memory);
//   assert |s''.memory| == |s'.memory|;

//   assert p'.commands == p.commands;
//   assert s'' == StateValue(s.pointer, memory);
//   assert p' == Program(p.commands, p'.pointer);
//   assert s == StateValue(s.pointer, s.memory);
//   assert p == Program(p.commands, p.pointer);
//   assert exists p'':Program, s': State:: p.commands == p''.commands && |s.memory| == |s'.memory| && 0 <= s'.pointer < |s'.memory|
//   && 0<= p''.pointer <= |p.commands| && max_steps(p, s, p'', s', input, 0, 0);
//   assert max_steps(p, s, p', s'', input, 0, 0);
// }
lemma ExistsAdvancedProgram(p: Program)
  requires 0 <= p.pointer < |p.commands|
  ensures exists p': Program :: 
            p'.commands == p.commands &&
            0 <= p.pointer < p'.pointer <= |p.commands|
{
  var p' := Program(p.commands, p.pointer + 1, p.input);
  assert p.pointer + 1 <= |p.commands|;
  assert p'.pointer == p.pointer + 1;
  assert p'.commands == p.commands;
}


lemma ExistsAdvancedIntermediate(ir: IntermediateRep)
  requires 0 <= ir.pointer < |ir.commands|
  ensures exists ir': IntermediateRep :: 
            ir'.commands == ir.commands &&
            0 <= ir.pointer < ir'.pointer <= |ir.commands|
{
  var ir' := IntermediateRep(ir.commands, ir.pointer + 1);
  assert ir.pointer + 1 <= |ir.commands|;
  assert ir'.pointer == ir.pointer + 1;
  assert ir'.commands == ir.commands;
}

lemma LemmaStrictlyIncreasing(s: seq<int>)
  requires |s| > 0
  requires forall i :: 1 <= i < |s| ==> s[i - 1] < s[i] 
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] 
{
  
  forall i, j | 0 <= i < j < |s| 
    ensures s[i] < s[j]
  {
    if j == i + 1 {
      assert s[i] < s[j];
    } else {
      assert i < j - 1;
      assert j - 1 < j;
      LemmaStrictlyIncreasing(s[..j]);
      assert s[i] < s[j-1]; 
      assert s[j-1] < s[j];
      assert s[i] < s[j];
    }
  }
}


lemma AllLessThanLast(s: seq<int>)
  requires |s| > 0 // Ensure the sequence is not empty
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] // Strictly increasing
  ensures forall i :: 0 <= i < |s| ==> s[i] <= s[|s| - 1] // All elements (except the last) are less than the last
{
}


}