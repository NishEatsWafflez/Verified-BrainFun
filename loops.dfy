include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"
include "triviallemmas.dfy"



module Loops {
import opened Lemmas
import opened Common
import opened Steps
import opened Equivalence
import opened Trivial

predicate valid_loop_ir(ir: IntermediateRep)
{
    valid_loop_ir_helper(ir.commands, 0, 0)
}
lemma SubArrayLoopSubArray(loop: seq<int>, commands: seq<Instr>)
requires |loop| >= 1
requires |commands| > 0
requires loop_less_than_commands(loop[..(|loop|-1)], commands)
requires loop[(|loop|-1)]==|commands|-1
ensures loop_less_than_commands(loop, commands)
{
    forall k | k in loop
    ensures 0 <= k < |commands|
    {
        if k in loop[..|loop|-1]{
            assert 0 <= k < |commands|;
        } else{
            assert k == loop[|loop|-1];
            assert 0 <= k < |commands|;
        }
    }
}
predicate valid_loop_ir_helper(ir: seq<Instr>, balance: int, i: int)
requires 0<=i<=|ir|
decreases |ir|-i
{
if |ir| == i then
    balance == 0
else 
    match ir[i]
        case Jump(k, true) => valid_loop_ir_helper(ir, balance + 1, i+1)
        case Jump(k, false) => balance > 0 && valid_loop_ir_helper(ir, balance - 1, i+1)
        case _ => valid_loop_ir_helper(ir, balance, i+1)
}

lemma aligned_implies_valid(p: Program, ir: IntermediateRep)
requires valid_loop_program(p)
requires valid_ir(ir)
requires valid_program(p)
requires aligned_instructions(p, ir)
ensures valid_loop_ir(ir)
{
    var indices := Changes(p);
    ChangeLemma(p, indices);
    aligned_implies_valid_helper(p, ir, 0, indices, 0, 0);
    assert valid_loop_ir_helper(ir.commands, 0, 0);
}

lemma addition_balance(p: Program, balance: int, p_index: int, new_balance: int, new_p: int)
requires valid_program(p)
requires 0<= p_index+1 <= |p.commands|
requires valid_loop_program_helper(p.commands, balance+1, p_index+1)
requires new_balance == balance+1
requires new_p == p_index+1
ensures valid_loop_program_helper(p.commands, new_balance, new_p)
{}

lemma addition_balance_k(p: Program, balance: int, p_index: int, new_balance: int, new_p: int, k:int)
requires valid_program(p)
requires 0<= p_index+k <= |p.commands|
requires valid_loop_program_helper(p.commands, balance, p_index+k)
requires new_balance == balance
requires new_p == p_index+k
ensures valid_loop_program_helper(p.commands, new_balance, new_p)
{}

lemma subtraction_balance(p: Program, balance: int, p_index: int, new_balance: int, new_p: int)
requires valid_program(p)
requires 0<= p_index+1 <= |p.commands|
requires valid_loop_program_helper(p.commands, balance-1, p_index+1)
requires new_balance == balance-1
requires new_p == p_index+1
ensures valid_loop_program_helper(p.commands, new_balance, new_p)
{}

lemma even_balance(p: Program, balance: int, p_index: int, new_balance: int, new_p: int)
requires valid_program(p)
requires 0<= p_index+1 <= |p.commands|
requires valid_loop_program_helper(p.commands, balance, p_index+1)
requires new_balance == balance
requires new_p == p_index+1
ensures valid_loop_program_helper(p.commands, new_balance, new_p)
{}

lemma aligned_implies_valid_helper(p: Program, ir: IntermediateRep, balance: int, indices: seq<int>, index: int, p_index: int)
requires 0 <= index <= |indices|
requires balance >= 0
requires indices == Changes(p)
requires changes_correct(p, indices)
requires valid_ir(ir)
requires valid_program(p)
requires aligned_instructions(p, ir)
decreases |indices|-index
requires (index == |indices| && p_index == |p.commands|) || (index < |indices| && p_index == indices[index]) 
requires valid_loop_program_helper(p.commands, balance, p_index)
ensures valid_loop_ir_helper(ir.commands, balance, index)
{
    if index == |indices|{
        assert index == |ir.commands|;
        assert valid_loop_ir_helper(ir.commands, balance, index);
    }else{
    var p_index := indices[index];
        match p.commands[p_index] 
            case '[' => {
                // assert balance >=0;
                assert (match ir.commands[index]
                    case Jump(_, true) => true
                    case _ => false
                );
                // assert ((!(index+1 in indices)&&indices[index]+1 == |p.commands| ) || (indices[index]+1 < |p.commands| && indices[index]+1 in indices));    
                if index+1 < |indices|{
                    assert index+1 < |indices|;
                    assert indices[index+1] == p_index+1;
                    // assert indices[index+1]
                }else{
                    LemmaStrictlyIncreasing(indices);
                    assert p_index+1 == |p.commands|;
                }

                assert valid_loop_program_helper(p.commands, balance+1, p_index+1);
                assert 0 <= index+1 <= |indices|;
                assert indices == Changes(p);
                assert changes_correct(p, indices);
                assert valid_ir(ir);
                assert valid_program(p);
                assert aligned_instructions(p, ir);
                assert ( p_index+1 == |p.commands|) || (index+1 < |indices| && p_index+1 == indices[index+1]);
                var new_b := balance+1;
                var new_p_ind := p_index+1;
                var new_ind := index+1;
                addition_balance(p, balance, p_index, new_b, new_p_ind);
                assert valid_loop_program_helper(p.commands, new_b, new_p_ind);
                assert (new_p_ind == |p.commands|) || (new_ind < |indices| && new_p_ind == indices[new_ind]);
                assert 0 <= new_ind <= |indices|;
                aligned_implies_valid_helper(p, ir, new_b, indices, new_ind, new_p_ind);
            }
            case ']' => {
                assert balance > 0;
                assert (match ir.commands[index]
                    case Jump(_, false) => true
                    case _ => false
                );
                if index+1 < |indices|{
                    assert index+1 < |indices|;
                    assert indices[index+1] == p_index+1;
                }else{
                    // assert 
                    LemmaStrictlyIncreasing(indices);
                    assert p_index+1 == |p.commands|;
                }
                assert valid_loop_program_helper(p.commands, balance-1, p_index+1);
                assert 0 <= index+1 <= |indices|;
                assert indices == Changes(p);
                assert changes_correct(p, indices);
                assert valid_ir(ir);
                assert valid_program(p);
                assert aligned_instructions(p, ir);
                assert ( p_index+1 == |p.commands|) || (index+1 < |indices| && p_index+1 == indices[index+1]);
                var new_b := balance-1;
                var new_p_ind := p_index+1;
                var new_ind := index+1;
                subtraction_balance(p, balance, p_index, new_b, new_p_ind);
                assert valid_loop_program_helper(p.commands, new_b, new_p_ind);
                assert (new_p_ind == |p.commands|) || (new_ind < |indices| && new_p_ind == indices[new_ind]);
                assert 0 <= new_ind <= |indices|;
                aligned_implies_valid_helper(p, ir, new_b, indices, new_ind, new_p_ind);

                // aligned_implies_valid_helper(p, ir, balance-1, indices, index+1, p_index+1);
            }
            case ',' => {
                assert (match ir.commands[index]
                    case Jump(_, _) => false
                    case UserInput => true
                    case _ => false
                );
                if index+1 < |indices|{
                    assert index+1 < |indices|;
                    assert indices[index+1] == p_index+1;
                }else{
                    // assert 
                    LemmaStrictlyIncreasing(indices);
                    assert p_index+1 == |p.commands|;
                }
                assert valid_loop_program_helper(p.commands, balance, p_index+1);
                assert 0 <= index+1 <= |indices|;
                assert indices == Changes(p);
                assert changes_correct(p, indices);
                assert valid_ir(ir);
                assert valid_program(p);
                assert aligned_instructions(p, ir);
                assert ( p_index+1 == |p.commands|) || (index+1 < |indices| && p_index+1 == indices[index+1]);
                var new_p_ind := p_index+1;
                var new_ind := index+1;
                var new_b := balance;
                even_balance(p, balance, p_index, new_b, new_p_ind);
                assert valid_loop_program_helper(p.commands, new_b, new_p_ind);
                assert (new_p_ind == |p.commands|) || (new_ind < |indices| && new_p_ind == indices[new_ind]);
                assert 0 <= new_ind <= |indices|;
                aligned_implies_valid_helper(p, ir, new_b, indices, new_ind, new_p_ind);
            }
            case '.' =>{
                assert (match ir.commands[index]
                    case Jump(_, _) => false
                    case Print => true
                    case _ => false
                );
                if index+1 < |indices|{
                    assert index+1 < |indices|;
                    assert indices[index+1] == p_index+1;
                }else{
                    // assert 
                    LemmaStrictlyIncreasing(indices);
                    assert p_index+1 == |p.commands|;
                }
                assert valid_loop_program_helper(p.commands, balance, p_index+1);
                assert 0 <= index+1 <= |indices|;
                assert indices == Changes(p);
                assert changes_correct(p, indices);
                assert valid_ir(ir);
                assert valid_program(p);
                assert aligned_instructions(p, ir);
                assert ( p_index+1 == |p.commands|) || (index+1 < |indices| && p_index+1 == indices[index+1]);
                var new_p_ind := p_index+1;
                var new_ind := index+1;
                var new_b := balance;
                even_balance(p, balance, p_index, new_b, new_p_ind);
                assert valid_loop_program_helper(p.commands, new_b, new_p_ind);
                assert (new_p_ind == |p.commands|) || (new_ind < |indices| && new_p_ind == indices[new_ind]);
                assert 0 <= new_ind <= |indices|;
                aligned_implies_valid_helper(p, ir, new_b, indices, new_ind, new_p_ind);
            }
            case '>'=>{
                ValidLoopMoveRight(p, ir, index, p_index, indices);
                // assert (match ir.commands[index]
                //     case Jump(_, _) => false
                //     case _ => true
                // );
                var k := count_consecutive_symbols(p, p_index);
                loop_helper_stays_constant(p, k, p_index, balance, '>');
                var new_p_ind := p_index+k;
                var new_b := balance;
                addition_balance_k(p, balance, p_index, new_b, new_p_ind, k);
            }
            case '<'=>{
                ValidLoopMoveLeft(p, ir, index, p_index, indices);
                // assert (match ir.commands[index]
                //     case Jump(_, _) => false
                //     case _ => true
                // );
                var k := count_consecutive_symbols(p, p_index);
                loop_helper_stays_constant(p, k, p_index, balance, '<');
                var new_p_ind := p_index+k;
                var new_b := balance;
                addition_balance_k(p, balance, p_index, new_b, new_p_ind, k);
            }
            case '+'=>{
                ValidLoopAdd(p, ir, index, p_index, indices);
                // assert (match ir.commands[index]
                //     case Jump(_, _) => false
                //     case _ => true
                // );
                var k := count_consecutive_symbols(p, p_index);
                loop_helper_stays_constant(p, k, p_index, balance, '+');
                var new_p_ind := p_index+k;
                var new_b := balance;
                addition_balance_k(p, balance, p_index, new_b, new_p_ind, k);
            }
            case '-'=>{
                ValidLoopSub(p, ir, index, p_index, indices);
                // assert (match ir.commands[index]
                //     case Jump(_, _) => false
                //     case _ => true
                // );
                var k := count_consecutive_symbols(p, p_index);
                loop_helper_stays_constant(p, k, p_index, balance, '-');
                var new_p_ind := p_index+k;
                var new_b := balance;
                addition_balance_k(p, balance, p_index, new_b, new_p_ind, k);
            }
            case _ => {
                assume {:axiom} false; //This is a very minor axiom to assert that there are only these 8 characters, 
                //for some reason it times out without this...
            }
    }
}

predicate loop_less_than_commands(loops_indices: seq<int>, commands: seq<Instr>)
{
    forall i:: i in loops_indices ==> 0 <= i < |commands| && (match commands[i]
        case Jump(_, true) => true
        case _ => false)
}

lemma IncreasingArrayDoesntAffectLoops(ir: seq<Instr>, loops: seq<int>, j: int)
requires |ir| > 1
requires 0<=j < |ir|
requires loop_less_than_commands(loops, ir[..j])
ensures loop_less_than_commands(loops, ir)
{}

lemma ValidLoopMoveRight (p: Program, ir: IntermediateRep, index: int, p_index: int, indices: seq<int>)
requires valid_program(p)
requires valid_ir(ir)
requires 0 <= index < |indices|
requires p_index == indices[index]
requires indices == Changes(p)
requires changes_correct(p, indices)
requires aligned_instructions(p, ir)
requires p.commands[p_index] == '>'
ensures (p_index+count_consecutive_symbols(p, p_index) == |p.commands|) 
    || (index+1 < |indices| && p_index+count_consecutive_symbols(p, p_index) == indices[index+1])
ensures (match ir.commands[index]
                    case Jump(_, _) => false
                    case _ => true
                )
{
    assert matched_command_with_ir(p, ir.commands, index, indices);
    assert (match ir.commands[index]
            case Jump(dest, true) =>
                p.commands[indices[index]] == '['
            case Jump(dest, false) => (
                p.commands[indices[index]] == ']'
            )
            case _ => true
        );
    var k := count_consecutive_symbols(p, p_index);
    if index+1 < |indices|{
        assert index+1 < |indices|;
        assert indices[index+1] == p_index+k;
    }else{
        // assert 
        LemmaStrictlyIncreasing(indices);
        assert p_index+k == |p.commands|;
    }
}
lemma ValidLoopMoveLeft (p: Program, ir: IntermediateRep, index: int, p_index: int, indices: seq<int>)
requires valid_program(p)
requires valid_ir(ir)
requires 0 <= index < |indices|
requires p_index == indices[index]
requires indices == Changes(p)
requires changes_correct(p, indices)
requires aligned_instructions(p, ir)
requires p.commands[p_index] == '<'
ensures (p_index+count_consecutive_symbols(p, p_index) == |p.commands|) 
    || (index+1 < |indices| && p_index+count_consecutive_symbols(p, p_index) == indices[index+1])
ensures (match ir.commands[index]
                    case Jump(_, _) => false
                    case _ => true
                )
{
    assert matched_command_with_ir(p, ir.commands, index, indices);
    assert (match ir.commands[index]
            case Jump(dest, true) =>
                p.commands[indices[index]] == '['
            case Jump(dest, false) => (
                p.commands[indices[index]] == ']'
            )
            case _ => true
        );
    var k := count_consecutive_symbols(p, p_index);
    if index+1 < |indices|{
        assert index+1 < |indices|;
        assert indices[index+1] == p_index+k;
    }else{
        // assert 
        LemmaStrictlyIncreasing(indices);
        assert p_index+k == |p.commands|;
    }
}

lemma ValidLoopAdd (p: Program, ir: IntermediateRep, index: int, p_index: int, indices: seq<int>)
requires valid_program(p)
requires valid_ir(ir)
requires 0 <= index < |indices|
requires p_index == indices[index]
requires indices == Changes(p)
requires changes_correct(p, indices)
requires aligned_instructions(p, ir)
requires p.commands[p_index] == '+'
ensures (p_index+count_consecutive_symbols(p, p_index) == |p.commands|) 
    || (index+1 < |indices| && p_index+count_consecutive_symbols(p, p_index) == indices[index+1])
ensures (match ir.commands[index]
                    case Jump(_, _) => false
                    case _ => true
                )
{
    assert matched_command_with_ir(p, ir.commands, index, indices);
    assert (match ir.commands[index]
            case Jump(dest, true) =>
                p.commands[indices[index]] == '['
            case Jump(dest, false) => (
                p.commands[indices[index]] == ']'
            )
            case _ => true
        );
    var k := count_consecutive_symbols(p, p_index);
    if index+1 < |indices|{
        assert index+1 < |indices|;
        assert indices[index+1] == p_index+k;
    }else{
        // assert 
        LemmaStrictlyIncreasing(indices);
        assert p_index+k == |p.commands|;
    }
}

lemma ValidLoopSub (p: Program, ir: IntermediateRep, index: int, p_index: int, indices: seq<int>)
requires valid_program(p)
requires valid_ir(ir)
requires 0 <= index < |indices|
requires p_index == indices[index]
requires indices == Changes(p)
requires changes_correct(p, indices)
requires aligned_instructions(p, ir)
requires p.commands[p_index] == '-'
ensures (p_index+count_consecutive_symbols(p, p_index) == |p.commands|) 
    || (index+1 < |indices| && p_index+count_consecutive_symbols(p, p_index) == indices[index+1])
ensures (match ir.commands[index]
                    case Jump(_, _) => false
                    case _ => true
                )
{
    assert matched_command_with_ir(p, ir.commands, index, indices);
    assert (match ir.commands[index]
            case Jump(dest, true) =>
                p.commands[indices[index]] == '['
            case Jump(dest, false) => (
                p.commands[indices[index]] == ']'
            )
            case _ => true
        );
    var k := count_consecutive_symbols(p, p_index);
    if index+1 < |indices|{
        assert index+1 < |indices|;
        assert indices[index+1] == p_index+k;
    }else{
        // assert 
        LemmaStrictlyIncreasing(indices);
        assert p_index+k == |p.commands|;
    }
}


predicate less_than_k(j: int, k: int)
{
    (0<=j<k)
}

lemma loop_helper_stays_constant (p: Program, k: int, p_index: int, balance: int, c: char)
requires 0<= p_index < |p.commands|
requires k >0
requires p_index+k <= |p.commands|
requires c == '>' || c == '<' || c == '+' || c== '-'
requires valid_loop_program_helper(p.commands, balance, p_index)
requires forall j:: less_than_k(j, k) ==> p.commands[p_index+j] == c
ensures valid_loop_program_helper(p.commands, balance, p_index+k)
{
    var i := 0;
    while i < k
    invariant i<=k
    invariant valid_loop_program_helper(p.commands, balance, p_index+i)
    {
        assert valid_loop_program_helper(p.commands, balance, p_index+i);
        assert less_than_k(i, k);
        assert p.commands[p_index+i]==c;
        assert valid_loop_program_helper(p.commands, balance, p_index+i+1);
        i := i+1;
        assert valid_loop_program_helper(p.commands, balance, p_index+i);
    }
    assert i==k;
    assert valid_loop_program_helper(p.commands, balance, p_index+i);
}

predicate valid_loop_program(p: Program)
{
    valid_loop_program_helper(p.commands, 0, 0)
}

predicate valid_loop_program_helper(p: seq<char>, balance: int, i: int)
requires 0<=i <= |p|
decreases |p|-i
{
if i == |p| then
    balance == 0
  else if p[i] == '[' then
    valid_loop_program_helper(p, balance + 1, i+1)
  else if p[i] == ']' then
    balance > 0 && valid_loop_program_helper(p, balance - 1, i+1)
  else
    valid_loop_program_helper(p, balance, i+1)
}
predicate non_merge_symbols(p: Program, res: seq<int>)
{
    forall i:: (0<=i<|p.commands| && (p.commands[i] == '[' || p.commands[i] == ']' || p.commands[i] == '.' || p.commands[i] == ',') 
    ==> (exists k:: 0<= k < |Changes(p)| && Changes(p)[k]==i))
}
predicate non_merged_aligned_helper(p: Program, ir: IntermediateRep, i: int)
requires 0 <= i < |p.commands|
requires |ir.commands| == |Changes(p)|
{
    
    exists k :: (0 <= k < |ir.commands| &&
    (match p.commands[i]
        case '[' =>
            (match ir.commands[k]
                case Jump(x, true) => true
                case _ => false
            )&& Changes(p)[k] == i
        case ']' =>
            (match ir.commands[k]
                case Jump(x, false) => true
                case _ => false
            )&& Changes(p)[k] == i
        case '.' =>
            (match ir.commands[k]
                case Print => true
                case _ => false
            )&& Changes(p)[k] == i
        case ',' =>
            (match ir.commands[k]
                case UserInput => true
                case _ => false
            )&& Changes(p)[k] == i
        case _ => true

    ))
}
predicate non_merged_aligned(p: Program, ir: IntermediateRep)
requires |ir.commands| == |Changes(p)|
{
    forall i:: (0 <= i < |p.commands| ==>
        non_merged_aligned_helper(p, ir, i)
    )
}

predicate subRepSubProgram(p: Program, ir: IntermediateRep, startProgram: int, startIR: int, endProgram: int, endIR: int,
p': Program, ir': IntermediateRep)
requires |Changes(p)| == |ir.commands|
{
    0 <= startProgram < endProgram < |p.commands|
    && 0<= startIR < endIR < |ir.commands|
    && Changes(p)[startIR] == startProgram
    && Changes(p)[endIR] == endProgram
    && p' == Program(p.commands[startProgram+1.. endProgram], 0, p.input)
    && ir' == IntermediateRep(ir.commands[startIR+1..endIR], 0, ir.input)
}



lemma strictlyIncreasing (s: seq<int>, i: int, j: int)
requires |s| > 0
requires strictly_increasing(s)
requires 0 <= i < |s|
requires 0 <= j < |s|
ensures s[i] < s[j] ==> i < j
{}



 

method Compile(p: Program)  returns (result: IntermediateRep)
  requires valid_program(p)
  requires valid_loop_program(p)
  requires |p.commands| > 0
  ensures true

{
    var i := 0;
    var commands := [];

    while i < |p.commands|
    decreases |p.commands|-i
    {
        {match p.commands[i]
            case '[' => {
                commands := commands + [Jump(0, true)];
            }
            case ']' => {
                commands := commands + [Jump(0, false)];
            }
            case _ => {
                commands := commands + [Print];
            }
        }
        i := i+1;
    }
    result := IntermediateRep(commands, 0, p.input);
}
}