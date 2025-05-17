include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"

module Lemmas{
    import opened Common 
    import opened Steps
    import opened Equivalence

    // lemma and_implies_one(p: Program, s: State, p': Program, s': State)
    // requires ( |s.memory| == |s'.memory| && s'.output == s.output&&
    //             (p.pointer < p'.pointer) && 0 <= p.pointer < p'.pointer <= |p.commands| &&
    //             (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == '>'))
    //             && (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == '>')))
    //             && (s'.memory == s.memory)
    //             && (0 <= s.pointer+p'.pointer-p.pointer < |s.memory| ==> s'.pointer == s.pointer + p'.pointer-p.pointer)
    //             && ((|s.memory|<= s.pointer+p'.pointer-p.pointer) ==> s'.pointer == |s.memory|-1))
    // ensures (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == '>'))
    // {}

    lemma ChangeHelperLemma(p: Program, i: int)
      requires 0 <= i <= |p.commands|
      ensures change_helper_correct(p, i, ChangesHelper(p, i))
    {
      assume false;
    }
    lemma ChangeLemma(p: Program)
    ensures forall i:: 0<= i< |Changes(p)| ==> 0<= Changes(p)[i] <|p.commands|
    ensures forall i:: 0 <= i < |Changes(p)|-1 && p.commands[Changes(p)[i]] in ['+', '-', '<', '>'] ==> Changes(p)[i+1]==Changes(p)[i]+ count_consecutive_symbols(p, Changes(p)[i])
    // ensures forall i:: i in Changes(p) && p.commands[i] in ['+', '-', '<', '>']  && i + count_consecutive_symbols(p, i) < |p.commands|==> i+ count_consecutive_symbols(p, i) in Changes(p)
    ensures forall d:: 0<= d <|Changes(p)|-1 && p.commands[Changes(p)[d]] in ['+', '-', '<', '>']==> ((p.commands[Changes(p)[d]]!=p.commands[Changes(p)[d+1]]))
    ensures forall d:: 0<= d <|Changes(p)|-1 && !(p.commands[Changes(p)[d]] in ['+', '-', '<', '>'])==> (Changes(p)[d+1]-Changes(p)[d] ==1)
    ensures forall d:: (d in Changes(p) && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) >= |p.commands|) || d+count_consecutive_symbols(p, d) in Changes(p))
    ensures forall d:: (d in Changes(p) && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 >= |p.commands|) || d+1 in Changes(p))
    {
      ChangeHelperLemma(p, 0);
    }

    lemma AlignmentMeansEquivalenceMoves(p: Program, s: State, ir: IntermediateRep, i: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    requires match ir.commands[i] {
      case Move(_) => true
      case _ => false
    }    
      ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 
    {
        ChangeLemma(p);
        var indices := Changes(p);      
        var index := indices[i];
        var currIr := IntermediateRep(ir.commands, i, ir.input);
        match ir.commands[i] 
          case Move(k) =>{
            // assume false;
            assert p.commands[index] in ['>', '<'];
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            if k >= 0{
              assert max_steps(p_by_k,s, p', s');


              assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '>'));
              assert index+k < |p.commands| ==> (p.commands[index] != p.commands[index+k]);
              assert forall j:: index <= j < index+k ==> p.commands[j] == p.commands[index]; 
              assert index == p_by_k.pointer;
              assert p'.pointer - p_by_k.pointer==k;
              IrStep(currIr, s);
              var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
              assert ir_step(currIr, s, ir', sIR);
              if (s.pointer + k >= |s.memory|){
                assert sIR.pointer == |s.memory|-1;
                assert s'.pointer == |s.memory|-1;

              } else if (s.pointer +k < 0){
                assert sIR.pointer == 0;
                assert s'.pointer == 0;
              } else {
                assert sIR.pointer == s.pointer +k;
                assert s'.pointer == s.pointer +k;
              }
              assert sIR.memory == s.memory;
              assert max_steps(p_by_k, s, p', s');
              assert p_by_k.commands[p_by_k.pointer]=='>';
              assert s'.memory==s'.memory;
              assert p'.pointer - p_by_k.pointer==k;
              assert s'.memory == sIR.memory;
              assert s'.output == s.output;
              assert sIR.output == s.output;
              assert s'.output == sIR.output;
              assert s'.pointer == sIR.pointer; 
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
              assert i < |Changes(p)|;
              assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
              assert max_steps(p_by_k, s, p', s');
              assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
              assert program_k_max_steps(p, s, p', s', i);
              assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
              assert sIR == s';
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
            }else{
              assert max_steps(p_by_k,s, p', s');
              assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '<'));
              assert index-k < |p.commands| ==> (p.commands[index] != p.commands[index-k]);
              assert forall j:: index <= j < index-k ==> p.commands[j] == p.commands[index]; 
              assert index == p_by_k.pointer;
              assert -p'.pointer + p_by_k.pointer==k;
              IrStep(currIr, s);
              var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
              assert ir_step(currIr, s, ir', sIR);
              if (s.pointer + k >= |s.memory|){
                assert sIR.pointer == |s.memory|-1;
                assert s'.pointer == |s.memory|-1;

              } else if (s.pointer +k < 0){
                assert sIR.pointer == 0;
                assert s'.pointer == 0;
              } else {
                assert sIR.pointer == s.pointer +k;
                assert s'.pointer == s.pointer +k;
              }
              assert sIR.memory == s.memory;
              assert max_steps(p_by_k, s, p', s');
              assert p_by_k.commands[p_by_k.pointer]=='<';
              assert s'.memory==s'.memory;
              assert p'.pointer - p_by_k.pointer==-k;
              assert s'.memory == sIR.memory;
              assert s'.output == s.output;
              assert sIR.output == s.output;
              assert s'.output == sIR.output;
              assert s'.pointer == sIR.pointer; 
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
              assert i < |Changes(p)|;
              assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
              assert max_steps(p_by_k, s, p', s');
              assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
              assert program_k_max_steps(p, s, p', s', i);
              assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
              assert sIR == s';
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
                      
            }
          
          }

    }

    lemma AlignmentMeansEquivalence(p: Program, s: State, ir: IntermediateRep)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    ensures EquivalentReps(p, s, ir)
    {
      // assume false;
      var indices := Changes(p);      
      forall i | within_ir_range(i, ir)
      ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 

      {

        var index := indices[i];
        var currIr := IntermediateRep(ir.commands, i, ir.input);
        match ir.commands[i] 
          case Inc(k) =>{
            // assume false;
            assert p.commands[index] in ['+', '-'];
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert forall j:: p_by_k.pointer <= j < p'.pointer ==> p_by_k.commands[indices[i]] == p_by_k.commands[j];
            if k >= 0{
              assert k==count_consecutive_symbols(p, index); 
              assert p.commands[index] == '+';
              assert index+k < |p.commands| ==> (p.commands[index] != p.commands[index+k]);
              // assert forall j:: index <= j < index+k ==> p.commands[j] == p.commands[index]; 
              assert index == p_by_k.pointer;
              assert p'.pointer - p_by_k.pointer==k;
              IrStep(currIr, s);
              var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
              assert ir_step(currIr, s, ir', sIR);
              
              assert s.pointer == sIR.pointer;
              assert s.pointer == s'.pointer;
              assert sIR.memory[sIR.pointer] == (s.memory[sIR.pointer]+k)%256;
              assert max_steps(p_by_k, s, p', s');
              assert p_by_k.commands[p_by_k.pointer]=='+';
              assert s'.memory[s'.pointer] == (s.memory[s.pointer]+ p'.pointer-p_by_k.pointer)%256;
              assert p'.pointer - p_by_k.pointer==k;
              assert s'.memory[s'.pointer] == (s.memory[s.pointer]+k)%256;
              assert s'.memory == sIR.memory;
              assert s'.output == s.output;
              assert sIR.output == s.output;
              assert s'.output == sIR.output;
              assert s'.pointer == sIR.pointer; 
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
              assert i < |Changes(p)|;
              assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
              assert max_steps(p_by_k, s, p', s');
              assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
              assert program_k_max_steps(p, s, p', s', i);
              assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
              assert sIR == s';
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
            }else{
              assert -k==count_consecutive_symbols(p, index); 
              assert p.commands[index] == '-';
              assert index-k < |p.commands| ==> (p.commands[index] != p.commands[index-k]);
              // assert forall j:: index <= j < index+k ==> p.commands[j] == p.commands[index]; 
              assert index == p_by_k.pointer;
              assert p'.pointer - p_by_k.pointer==-k;
              IrStep(currIr, s);
              var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
              assert ir_step(currIr, s, ir', sIR);
              
              assert s.pointer == sIR.pointer;
              assert s.pointer == s'.pointer;
              assert sIR.memory[sIR.pointer] == (s.memory[sIR.pointer]+k)%256;
              assert max_steps(p_by_k, s, p', s');
              assert p_by_k.commands[p_by_k.pointer]=='-';
              assert s'.memory[s'.pointer] == (s.memory[s.pointer]- p'.pointer+p_by_k.pointer)%256;
              assert p'.pointer - p_by_k.pointer==-k;
              assert s'.memory[s'.pointer] == (s.memory[s.pointer]+k)%256;
              assert s'.memory == sIR.memory;
              assert s'.output == s.output;
              assert sIR.output == s.output;
              assert s'.output == sIR.output;
              assert s'.pointer == sIR.pointer; 
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
              assert i < |Changes(p)|;
              assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
              assert max_steps(p_by_k, s, p', s');
              assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
              assert program_k_max_steps(p, s, p', s', i);
              assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
              assert sIR == s';
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
                        
            }
            // assert forall j:: index <= j < index+k ==> p.commands[j] == p.commands[index];
            // assert p_by_k.commands==p.commands;
            // assert count_consecutive_symbols(p, index)==count_consecutive_symbols(p_by_k, index);
           
            // assert forall j:: 0<=j<k ==> (index+j < |p.commands|) && p.commands[index+j] == p.commands[index];

          } 
          case Move(k) =>{
            AlignmentMeansEquivalenceMoves(p, s, ir, i);

            // assume false;
            /*assert p.commands[index] in ['>', '<'];
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            if k >= 0{
              assert max_steps(p_by_k,s, p', s');

              // assert (|s.memory| == |s'.memory| && s'.output == s.output&&
              //   (p_by_k.pointer < p'.pointer)&&
              //   (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '>'))
              //   && (p'.pointer == |p_by_k.commands| || (p'.pointer < |p_by_k.commands| ==> !(p_by_k.commands[p'.pointer] == '>')))
              //   && (s'.memory == s.memory)
              //   && (0 <= s.pointer+p'.pointer-p_by_k.pointer < |s.memory| ==> s'.pointer == s.pointer + p'.pointer-p_by_k.pointer))
              //   // && (0 > s.pointer+count_commands(p, p', ['>', '<']) ==> s'.pointer == 0)
              //   && ((|s.memory|<= s.pointer+p'.pointer-p_by_k.pointer) ==> s'.pointer == |s.memory|-1);
              // assert max_steps(p_by_k, s, p', s') ==> (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '>'));
              assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '>'));
              // assert forall j:: p_by_k.pointer <= j < p'.pointer ==> p_by_k.commands[j] == '>';
              assert index+k < |p.commands| ==> (p.commands[index] != p.commands[index+k]);
              assert forall j:: index <= j < index+k ==> p.commands[j] == p.commands[index]; 
              assert index == p_by_k.pointer;
              assert p'.pointer - p_by_k.pointer==k;
              IrStep(currIr, s);
              var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
              assert ir_step(currIr, s, ir', sIR);
              if (s.pointer + k >= |s.memory|){
                assert sIR.pointer == |s.memory|-1;
                assert s'.pointer == |s.memory|-1;

              } else if (s.pointer +k < 0){
                assert sIR.pointer == 0;
                assert s'.pointer == 0;
              } else {
                assert sIR.pointer == s.pointer +k;
                assert s'.pointer == s.pointer +k;
              }
              assert sIR.memory == s.memory;
              assert max_steps(p_by_k, s, p', s');
              assert p_by_k.commands[p_by_k.pointer]=='>';
              assert s'.memory==s'.memory;
              assert p'.pointer - p_by_k.pointer==k;
              // assert s'.memory[s'.pointer] == (s.memory[s.pointer]+k)%256;
              assert s'.memory == sIR.memory;
              assert s'.output == s.output;
              assert sIR.output == s.output;
              assert s'.output == sIR.output;
              assert s'.pointer == sIR.pointer; 
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
              assert i < |Changes(p)|;
              assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
              assert max_steps(p_by_k, s, p', s');
              assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
              assert program_k_max_steps(p, s, p', s', i);
              assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
              assert sIR == s';
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
            }else{
              assert max_steps(p_by_k,s, p', s');

              // assert (|s.memory| == |s'.memory| && s'.output == s.output&&
              //   (p_by_k.pointer < p'.pointer)&&
              //   (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '<'))
              //   && (p'.pointer == |p_by_k.commands| || (p'.pointer < |p_by_k.commands| ==> !(p_by_k.commands[p'.pointer] == '<')))
              //   && (s'.memory == s.memory)
              //   && (0 <= s.pointer-p'.pointer+p_by_k.pointer < |s.memory| ==> s'.pointer == s.pointer - p'.pointer+p_by_k.pointer))
              //   // && (0 > s.pointer+count_commands(p, p', ['>', '<']) ==> s'.pointer == 0)
              //   && ((0>= s.pointer-p'.pointer+p_by_k.pointer) ==> s'.pointer == 0);
              // assert max_steps(p_by_k, s, p', s') ==> (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '>'));
              assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '<'));
              // assert forall j:: p_by_k.pointer <= j < p'.pointer ==> p_by_k.commands[j] == '>';
              assert index-k < |p.commands| ==> (p.commands[index] != p.commands[index-k]);
              assert forall j:: index <= j < index-k ==> p.commands[j] == p.commands[index]; 
              assert index == p_by_k.pointer;
              assert -p'.pointer + p_by_k.pointer==k;
              IrStep(currIr, s);
              var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
              assert ir_step(currIr, s, ir', sIR);
              if (s.pointer + k >= |s.memory|){
                assert sIR.pointer == |s.memory|-1;
                assert s'.pointer == |s.memory|-1;

              } else if (s.pointer +k < 0){
                assert sIR.pointer == 0;
                assert s'.pointer == 0;
              } else {
                assert sIR.pointer == s.pointer +k;
                assert s'.pointer == s.pointer +k;
              }
              assert sIR.memory == s.memory;
              assert max_steps(p_by_k, s, p', s');
              assert p_by_k.commands[p_by_k.pointer]=='<';
              assert s'.memory==s'.memory;
              assert p'.pointer - p_by_k.pointer==-k;
              // assert s'.memory[s'.pointer] == (s.memory[s.pointer]+k)%256;
              assert s'.memory == sIR.memory;
              assert s'.output == s.output;
              assert sIR.output == s.output;
              assert s'.output == sIR.output;
              assert s'.pointer == sIR.pointer; 
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
              assert i < |Changes(p)|;
              assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
              assert max_steps(p_by_k, s, p', s');
              assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
              assert program_k_max_steps(p, s, p', s', i);
              assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
              assert sIR == s';
              assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
                      
            }*/
          
          }
          case Print =>{
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            IrStep(currIr, s);  
            var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
            assert sIR.memory == s.memory;
            assert sIR == s';          
          }
          case UserInput =>{
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            IrStep(currIr, s);  
            var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
            // assert sIR.memory == s.memory;
            assert sIR == s';          
          }
          
          case _ => {assume {:axiom} false;}
          assert exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;

      }

      assert EquivalentReps(p, s, ir);

    }



lemma IrStep(ir: IntermediateRep, s: State)
    requires state_reqs(s)
    requires valid_input(ir.input)
    requires valid_ir(ir)
    decreases |ir.commands| - ir.pointer //Need to figure out how to prove decreases or termination as we descend into recursion :0
    ensures exists ir': IntermediateRep, s': State :: valid_state(s, s') && state_reqs(s') && in_sync_irs(ir, ir') && valid_ir(ir') && ir_step(ir, s, ir', s') && valid_input(ir'.input)
{
    if ir.pointer == |ir.commands| {
        var ir' := ir;
        var s' := s;
        assert state_reqs(s') && ir_step(ir, s, ir', s');
    }else{
        // assert loop_depth(ir) == 1 ==> (ir.commands[ir.pointer] is Instr);

        match ir.commands[ir.pointer]
            case Inc(n) =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var mem := s.memory;
                mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+n)%256] + mem[s.pointer+1..];
                var s' := StateValue(s.pointer, mem, s.output);
                // assert ir'.commands == ir.commands;
                assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
            }
            case Move(n) =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var pt := s.pointer;
                if pt+n >= |s.memory|{
                    pt := |s.memory|-1;
                }else if pt+n <0{
                    pt := 0;
                }else{
                    pt := pt+n;
                }
                var s' := StateValue(pt, s.memory, s.output);
                assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
                
            }
            case Print =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var s' := StateValue(s.pointer, s.memory, s.output+ [s.memory[s.pointer] as char]);
                assert state_reqs(s') &&valid_state(s, s') && ir_step(ir, s, ir', s');
            }
            case UserInput =>{
                if |ir.input| == 0{
                    var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                    assert ir_moved_up(ir, ir');
                    var mem := s.memory;
                    mem :=   mem[..s.pointer] + [' ' as int] + mem[s.pointer+1..];
                    assert mem[s.pointer] == ' ' as int;
                    var s' := StateValue(s.pointer, mem, s.output);
                    assert s'.memory[s.pointer] == ' ' as int;
                    assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
                } else if |ir.input| > 0{
                    var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input[1..]);
                    assert ir_moved_up(ir, ir');
                    var mem := s.memory;
                    mem :=   mem[..s.pointer] + [ir.input[0] as int] + mem[s.pointer+1..];
                    assert mem[s.pointer] == ir.input[0] as int;
                    var s' := StateValue(s.pointer, mem, s.output);
                    assert s'.memory[s.pointer] == ir.input[0] as int;
                    assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');   
                }
            }
            case Jump(dest, direction) =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var s' := s;
                assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
            }    
            
    }
}

lemma MaxSteps(p: Program, s: State)
  requires 0 <= p.pointer <= |p.commands|
  requires valid_program(p)
  requires state_reqs(s)
  requires valid_input(p.input)
//   requires enough_input(p)
  requires 0 <= s.pointer < |s.memory|
  ensures exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    
    if p.pointer == |p.commands| {
        var p' := p;
        var s' := s;
        assert (exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s'));

    }else{
    if p.commands[p.pointer] == '+' || p.commands[p.pointer] == '-' {MaxStepsPlusMinus(p, s);}
    else if p.commands[p.pointer] in ['>', '<']{   MaxStepsMove(p, s);}
    else if p.commands[p.pointer] == '.'{   MaxStepsPrint(p, s);}
    else if p.commands[p.pointer] == ','{   
        
        MaxStepsInput(p, s);}
    else if p.commands[p.pointer] == '['{   MaxStepsStartLoop(p, s);}
    else if p.commands[p.pointer] == ']'{   MaxStepsEndLoop(p, s);}
    }
    assert (exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') && valid_input(p'.input));
}

lemma MaxStepsPlusMinus(p: Program, s: State)
  requires 0 <= p.pointer < |p.commands|
  requires valid_program(p)
//   requires enough_input(p)
  requires valid_input(p.input)
  requires state_reqs(s)
  requires p.commands[p.pointer] in ['+', '-']
  requires 0 <= s.pointer < |s.memory|
  ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    var i := p.pointer+1;
    while i < |p.commands| && p.commands[i] ==p.commands[p.pointer]
    decreases |p.commands|-i
    invariant i <= |p.commands|
    invariant forall j:: p.pointer <= j < i ==> p.commands[j] == p.commands[p.pointer]
    {
        i := i+1;
    }
    var mem := s.memory;
    // var newVal := s.memory[s.pointer];
    // assert enough_input(p);
    /*assert forall j:: p.pointer <= j < i ==> p.commands[j] != ',';
    var s2 := set j| p.pointer <= j < i && p.commands[j]==',';
    assert forall j:: p.pointer <= j < i ==> (!(j in s2));
    var s3 := set j | i <= j < |p.commands| && p.commands[j] == ',';
    var s4 := set j | p.pointer <= j < |p.commands| && p.commands[j]==',';
    assert s4 == s2+s3;
    assert |s4| == |s2|+|s3|;
    // assert forall j :: p.pointer <= j < i ==> !(j in s2);
    assert |s2|==0;*/
    var p' := Program(p.commands, i, p.input);
    // assert enough_input(p');
    // count := count_commands(p, p', ['+', '-']);
    if p.commands[p.pointer] == '+'{
      mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+p'.pointer-p.pointer)%256] + mem[s.pointer+1..];
      assert mem[s.pointer] == (s.memory[s.pointer]+p'.pointer-p.pointer)%256;
    }else if p.commands[p.pointer]=='-'{
      mem :=   mem[..s.pointer] + [(s.memory[s.pointer]-p'.pointer+p.pointer)%256] + mem[s.pointer+1..];
      assert mem[s.pointer] == (s.memory[s.pointer]-p'.pointer+p.pointer)%256;


    }
    var s' := StateValue(s.pointer, mem, s.output);
    assert valid_program(p') && aligned_programs(p, p');
    assert state_reqs(s');
    assert (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] ==p.commands[p.pointer]));
    assert (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == p.commands[p.pointer])));
    assert (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i]);
    // assert count == count_commands(p, p', ['+', '-']);
    assert valid_input(p'.input);
    assert p.commands[p.pointer] == '+' ==> s'.memory[s.pointer] == (s.memory[s.pointer]+p'.pointer-p.pointer)%256;
    assert p.commands[p.pointer] == '-'==>(s'.memory[s.pointer] == (s.memory[s.pointer]-p'.pointer+p.pointer)%256);
    assert max_steps(p, s, p', s');
}

lemma MaxStepsPrint(p: Program, s: State)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_input(p.input)
    requires 0 <= p.pointer < |p.commands|
    requires p.commands[p.pointer] == '.'
    ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    var out := s.output;
    out := out + [s.memory[s.pointer] as char];
    var s' := StateValue(s.pointer, s.memory, out);
    var p' := Program(p.commands, p.pointer+1, p.input);
    assert p'.pointer == p.pointer+1;
    assert p'.commands == p.commands;
    assert pointer_moved_up(p, p');
    assert valid_program(p) && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p) && program_step(s, p, s', p');
    assert max_steps(p, s, p', s');
}

lemma MaxStepsInput(p: Program, s: State)
    requires valid_program(p)
    requires state_reqs(s)
    requires 0 <= p.pointer < |p.commands|
    requires p.commands[p.pointer] == ','

    requires valid_input(p.input)
    ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    var mem := s.memory;
    // var newVal := s.memory[s.pointer];
    if |p.input| > 0{
        var p' := Program(p.commands, p.pointer+1, p.input[1..]);
        assert p.input[0] as int <= 255;
        mem :=   mem[..s.pointer] + [p.input[0] as int] + mem[s.pointer+1..];
        var s' := StateValue(s.pointer, mem, s.output);
        assert p'.pointer == p.pointer+1;
        assert p'.commands == p.commands;
        // assert forall j :: p.pointer <= j < i ==> !(j in s2);
        // assert |s2|==0;
        assert pointer_moved_up(p, p');
        assert valid_program(p) && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p) && program_step(s, p, s', p');
        assert max_steps(p, s, p', s');
    }else{
        var p' := Program(p.commands, p.pointer+1, p.input);
        mem :=   mem[..s.pointer] + [' ' as int] + mem[s.pointer+1..];
        var s' := StateValue(s.pointer, mem, s.output);
        assert p'.pointer == p.pointer+1;
        assert p'.commands == p.commands;
        // assert forall j :: p.pointer <= j < i ==> !(j in s2);
        // assert |s2|==0;
        assert pointer_moved_up(p, p');
        assert valid_program(p) && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p) && program_step(s, p, s', p');
        assert max_steps(p, s, p', s');
    }

}

/*lemma MaxStepsStartLoop(p: Program, s: State)
    requires valid_program(p)
    requires state_reqs(s)
    requires 0 <= p.pointer < |p.commands|-1
    requires p.commands[p.pointer] == '['
    // ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') 
{
    assert balanced_brackets(p);
    if s.memory[s.pointer] > 0{
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
    }else{
        var i := p.pointer+1;
        var count := 0;

        while (i < |p.commands| && (p.commands[i] != ']' || count != 1))
            decreases |p.commands|-i
            invariant i <= |p.commands|
            // invariant count >= 0
        {
            if p.commands[i] == '[' {count := count + 1;}
            else if p.commands[i] == ']' {count := count - 1;}
            i := i+1;
        }
        assert i < |p.commands|;
        var p' := Program(p.commands, i+1, p.input);
    }
}*/

//  lemma MaxStepsStartLoop(p: Program, s: State)
//         requires valid_program(p)
//         requires state_reqs(s)
//         requires 0 <= p.pointer < |p.commands|-1
//         requires p.commands[p.pointer] == '['
//         requires MatchingBracketExists(p.commands, p.pointer)
//         // ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') 
//     {
//         assert balanced_brackets(p);
//         if s.memory[s.pointer] > 0{
//             var p' := Program(p.commands, p.pointer+1, p.input);
//             assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
//         }else{
//             var index := FindMatchingBracketIndex(p.commands, p.pointer+1)+1;
//             var p' := Program(p.commands, index, p.input);
//             assert 0 <= index <= |p.commands|;
//             assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
//         }
//     }
lemma MaxStepsStartLoop(p: Program, s: State)
        requires valid_program(p)
        requires state_reqs(s)
        requires 0 <= p.pointer < |p.commands|
        requires p.commands[p.pointer] == '['
        requires valid_input(p.input)
        ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
    {
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert pointer_moved_up(p, p');

        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
    }

lemma MaxStepsEndLoop(p: Program, s: State)
        requires valid_program(p)
        requires state_reqs(s)
        requires 0 <= p.pointer < |p.commands|
        requires p.commands[p.pointer] == ']'
        requires valid_input(p.input)
        ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
    {
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert pointer_moved_up(p, p');

        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
    }

lemma MaxStepsMove(p: Program, s: State)
  requires 0 <= p.pointer < |p.commands|
  requires valid_program(p)
  requires state_reqs(s)
  requires p.commands[p.pointer] in ['<', '>']
  requires 0 <= s.pointer < |s.memory|
  requires valid_input(p.input)
  ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') && valid_input(p'.input)
{
  var i := p.pointer+1;
    while i < |p.commands| && p.commands[i] ==p.commands[p.pointer]
    decreases |p.commands|-i
    invariant i <= |p.commands|
    invariant forall j:: p.pointer <= j < i ==> p.commands[j] == p.commands[p.pointer]
    {
        i := i+1;
    }
    var mem := s.memory;
    // var newVal := s.memory[s.pointer];
    // assert enough_input(p);
    /*assert forall j:: p.pointer <= j < i ==> p.commands[j] != ',';
    var s2 := set j| p.pointer <= j < i && p.commands[j]==',';
    assert forall j:: p.pointer <= j < i ==> (!(j in s2));
    var s3 := set j | i <= j < |p.commands| && p.commands[j] == ',';
    var s4 := set j | p.pointer <= j < |p.commands| && p.commands[j]==',';
    assert s4 == s2+s3;
    assert |s4| == |s2|+|s3|;
    // assert forall j :: p.pointer <= j < i ==> !(j in s2);
    assert |s2|==0;*/
    var p' := Program(p.commands, i, p.input);
    // assert enough_input(p');
    // count := count_commands(p, p', ['+', '-']);
    var count := 0;
    if p.commands[p.pointer] == '>'{
      count := p'.pointer-p.pointer;
      // mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+p'.pointer-p.pointer)%256] + mem[s.pointer+1..];
    }else if p.commands[p.pointer]=='<'{
      count := p.pointer-p'.pointer;
      // mem :=   mem[..s.pointer] + [(s.memory[s.pointer]-p'.pointer+p.pointer)%256] + mem[s.pointer+1..];

    }
    
    var point := s.pointer;
    assert 0 <= point;
    if point + count >= |s.memory|{
        point := |s.memory|-1;
    }else if point + count <= 0{
        point := 0;
    }else{
        point := point+count;
    }
    assert point < |s.memory|;
    var s' := StateValue(point, s.memory, s.output);
    assert valid_program(p') && aligned_programs(p, p');
    assert state_reqs(s');
    assert (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == p.commands[p.pointer]));
    assert (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == p.commands[p.pointer])));
    assert (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i]);
    assert max_steps(p, s, p', s');
}

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
  var ir' := IntermediateRep(ir.commands, ir.pointer + 1, ir.input);
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