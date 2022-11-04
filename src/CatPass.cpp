#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/Local.h"
#include <set>
#include <list>
#include <iostream>
#include <map>
#include <unordered_set>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <queue>
using namespace llvm;
using namespace std;
namespace {
  struct CAT : public FunctionPass {
    static char ID;
    unordered_map<int, Instruction*> OrderSsaVar; 
    unordered_map<Instruction*, BitVector> cluster;
    unsigned ssaVarCnt = 0;
    unordered_map<Instruction*, int> ssaVarOrder;
    unordered_map<int, BitVector> ssaVarCluster;
    unordered_map<Instruction*, BitVector> GEN, KILL, IN, OUT;
    queue<Instruction*> q;
    set<StringRef> catFuncName;
    unordered_map<CallInst*, int> last_int;
    CAT() : FunctionPass(ID) {}

    // This function is INvoked once at the INitialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      catFuncName.insert("CAT_new");
      catFuncName.insert("CAT_add");
      catFuncName.insert("CAT_sub");
      catFuncName.insert("CAT_set");
      return false;
    }
   
    void addLabel(CallInst *INst) 
    {
      OrderSsaVar[ssaVarCnt] = INst;
      ssaVarOrder[INst] = ssaVarCnt++;
    }
    
    void setBitVector() 
    {
      for(auto &[INst, label] : ssaVarOrder) 
      {
        BitVector vec(ssaVarCnt, false);
        vec[label] = true;
        cluster[INst] = vec;
      }
    }

    void setCluster(CallInst *INst) 
    {
      auto fun_name = INst->getCalledFunction()->getName();
      if(fun_name == "CAT_new") 
      {
        ssaVarCluster[ssaVarOrder[INst]] |= cluster[INst];
      } 
      else if(catFuncName.count(fun_name))
      {
        auto first_Op = INst->getOperand(0);
        if(isa<PHINode>(first_Op)) 
        {
          auto phi = cast<PHINode>(first_Op);
          for(unsigned i = 0; i < phi->getNumOperands(); i++) 
          {
            if(isa<CallInst>(phi->getIncomingValue(i))) 
            {
              ssaVarCluster[ssaVarOrder[cast<CallInst>(phi->getOperand(i))]] |= cluster[INst];
            }
          }
        } 
        else if(isa<CallInst>(first_Op) && cast<CallInst>(first_Op)->getCalledFunction()->getName() == "CAT_new") 
        {
            auto origIN_INst = cast<Instruction>(INst->getArgOperand(0));
            ssaVarCluster[ssaVarOrder[origIN_INst]] |= cluster[INst];
        }
      } 
      else if(fun_name != "CAT_get")
      { 
        unsigned n = INst->getNumOperands();
        for(unsigned i = 0; i < n; i++) 
        {
          auto op = INst->getOperand(i);
          if(isa<CallInst>(op) && catFuncName.count(cast<CallInst>(op)->getCalledFunction()->getName())) 
          {
            auto catInst = cast<CallInst>(op);
            if(catInst->getCalledFunction()->getName() == "CAT_new") 
            {
              ssaVarCluster[ssaVarOrder[catInst]] |= cluster[INst];
            } 
            else if(catFuncName.count(catInst->getCalledFunction()->getName())) 
            {
              auto cat_new = dyn_cast<CallInst>(catInst->getOperand(0));
              if(cat_new && cat_new->getCalledFunction()->getName() == "CAT_new") 
              {
                ssaVarCluster[ssaVarOrder[cat_new]] |= cluster[INst];
              }
            }
          }
        }
      }
    }

    void setGENAndKILL(Instruction *INst) 
    {
      StringRef fun_name;
      if(isa<CallInst>(INst)) fun_name = cast<CallInst>(INst)->getCalledFunction()->getName();
      else if(auto store_INst = dyn_cast<StoreInst>(INst)) 
      {
        GEN[INst] = cluster[INst];
        KILL[INst] = BitVector(ssaVarCnt, false);
        if(auto cat_cal = dyn_cast<CallInst>(store_INst->getValueOperand())) 
        {
          if(catFuncName.count(cat_cal->getCalledFunction()->getName())) 
          {
            KILL[INst] = cluster[cat_cal];
          }
        }
        return;
      }else 
      {
        GEN[INst] = BitVector(ssaVarCnt, false);
        KILL[INst] = BitVector(ssaVarCnt, false);
        return;
      }
      BitVector bit_vec(ssaVarCnt, false); 
      if(fun_name == "CAT_new") 
      {
        bit_vec = ssaVarCluster[ssaVarOrder[INst]];
        GEN[INst] = cluster[INst];
      } else if(catFuncName.count(fun_name)) {

        auto cat_new = INst->getOperand(0);
        if(auto phi = dyn_cast<PHINode>(cat_new)) 
        {
          //bit_vec |= cluster[INst];
          for(unsigned i = 0; i < phi->getNumOperands(); i++) 
          {
            auto cat_new = phi->getOperand(i);
            if(auto call_new = dyn_cast<CallInst>(cat_new)) 
            {
              bit_vec |= ssaVarCluster[ssaVarOrder[call_new]];
            } 
          }
        } 
        else if(isa<CallInst>(INst->getOperand(0))) 
        {
          CallInst *cal_INst = cast<CallInst>(INst->getOperand(0));
          bit_vec = ssaVarCluster[ssaVarOrder[cal_INst]];
        }
        GEN[INst] = cluster[INst];
      } 
      else if(fun_name != "CAT_get") 
      {
        unsigned n = INst->getNumOperands();
        for(unsigned i = 0; i < n; i++) 
        {
          auto INst_op = INst->getOperand(i);
          if(isa<CallInst>(INst_op) && (cast<CallInst>(INst_op)->getCalledFunction()->getName() == "CAT_new")) 
          {
            GEN[INst] = cluster[INst];
          } 
        }
      }
      if(catFuncName.count(fun_name)) 
      {
        bit_vec ^= cluster[INst];
        KILL[INst] = bit_vec;
      } 
      else 
      {
        KILL[INst] = BitVector(ssaVarCnt, false);
      }
    }

    
    void setINAndOUT(Function &F) 
    {
      for(auto &INst : instructions(F)) 
      {
          setGENAndKILL(&INst);
      }
      for(auto &INst : instructions(F)) 
      {
        q.push(&INst);
      } 
      while(!q.empty()) 
      {
        auto &INst = q.front();
        auto bb = INst->getParent();
        q.pop();
        BitVector IN_bit(ssaVarCnt, false), OUT_bit(ssaVarCnt, false);
        BitVector GEN_bit = GEN[INst], KILL_bit = KILL[INst];
        auto oldOUT = OUT[INst];
        if(&bb->front() == INst) 
        {
          for(auto prev : predecessors(bb)) 
          {
            auto INst_prev = prev->getTerminator();
            IN_bit |= OUT[INst_prev];
          }
        } 
        else 
        {
          IN_bit = OUT[INst->getPrevNode()];
        }
        OUT_bit = IN_bit;
        OUT_bit |= GEN_bit;
        OUT_bit &= KILL_bit.flip();
        IN[INst] = IN_bit;
        OUT[INst] = OUT_bit;
        if(OUT_bit != oldOUT) {
          if(INst == bb->getTerminator()) 
          {
            for(auto next : successors(bb)) 
            {
              q.push(&next->front());
            }
          } 
          else 
          {
            q.push(INst->getNextNode());
          }
        }
      }
    }
    void optimizeFunction(Function &F) 
    {
      queue<CallInst*> work_list;
      for(auto &INst : instructions(F)) 
      {
        if(auto cal_INst = dyn_cast<CallInst>(&INst)) 
        {
          work_list.push(cal_INst);
        }
      }
      if(work_list.empty()) return;
      vector<BasicBlock*> bb_list;
      unordered_set<CallInst*>del_list;
      do 
      {
        auto cal_INst = work_list.front();
        errs()<<*cal_INst<<"\n";
        work_list.pop();
        StringRef f_name = cal_INst->getCalledFunction()->getName();
        if(f_name == "CAT_get" && isa<CallInst>(cal_INst->getOperand(0))) 
        {
          auto d1 = cast<CallInst>(cal_INst->getOperand(0));
          BitVector IN1 = IN[cal_INst], d1_set = ssaVarCluster[ssaVarOrder[d1]];
          d1_set &= IN1;
          unordered_set<ConstantInt*> result_set;
          int IN_count = 0;
          for(unsigned i = 0; i < ssaVarCnt; i++) 
          {
            if(d1_set[i] == 1) IN_count++;
          }
          for(unsigned i = 0; i < ssaVarCnt; i++) 
          {
            if(d1_set[i] == 1) {
              StringRef name = dyn_cast<CallInst>(OrderSsaVar[i])->getCalledFunction()->getName();
              if(name == "CAT_new") 
              {
                auto result = dyn_cast<ConstantInt>(OrderSsaVar[i]->getOperand(0));
                if(result) {
                   result_set.insert(result);
                   IN_count--;
                } 

              } 
              else if(name == "CAT_add" || name == "CAT_sub") 
              {
                if(isa<ConstantInt>(OrderSsaVar[i]->getOperand(1)) && isa<ConstantInt>(OrderSsaVar[i]->getOperand(2))) 
                {
                  if(name == "CAT_add") {
                    auto const1 = cast<ConstantInt>(OrderSsaVar[i]->getOperand(1))->getSExtValue();
                    auto const2 = cast<ConstantInt>(OrderSsaVar[i]->getOperand(2))->getSExtValue();
                    auto result = ConstantInt::get(IntegerType::get(F.getParent()->getContext(), 32), const1 + const2);
                    result_set.insert(result);
                    IN_count--;
                  }
                  else 
                  {
                    auto const1 = cast<ConstantInt>(OrderSsaVar[i]->getOperand(1))->getSExtValue();
                    auto const2 = cast<ConstantInt>(OrderSsaVar[i]->getOperand(2))->getSExtValue();
                    auto result = ConstantInt::get(IntegerType::get(F.getParent()->getContext(), 32), const1 - const2);
                    result_set.insert(result);
                    IN_count--;
                  }
                } 
              } 
              else if(name == "CAT_set") 
              {
                if(isa<ConstantInt>(OrderSsaVar[i]->getOperand(1))) 
                {
                  auto result = dyn_cast<ConstantInt>(OrderSsaVar[i]->getOperand(1));
                  if(result) 
                  {
                    result_set.insert(result);
                    IN_count--;
                  }
                }
              }
            }
          }
          if(result_set.size() == 1 && IN_count == 0) 
          {
              cal_INst->replaceAllUsesWith(*result_set.begin());
              cal_INst->eraseFromParent();
          }
        } 
        else if(f_name == "CAT_get" && isa<PHINode>(cal_INst->getOperand(0))) 
        {
          unordered_set<ConstantInt*> result_set;
          auto phi_node = cast<PHINode>(cal_INst->getOperand(0));
          //errs() << *phi_node;
          unsigned IN_count = 0;
          for(unsigned i = 0 ; i < phi_node->getNumOperands(); i++) 
          {
            //errs() << *phi_node->getIncomingValue(i) << "\n";
            if(isa<ConstantInt>(phi_node->getIncomingValue(i))) 
            {
              result_set.insert(cast<ConstantInt>(phi_node->getIncomingValue(i)));
              IN_count++;
            } 
          }
          errs()<<result_set.size()<<" "<<IN_count<<"\n";
          if(result_set.size() == 1 && phi_node->getNumOperands() == IN_count) 
          {
            phi_node->replaceAllUsesWith(*result_set.begin());
          }
        } 
        else if((f_name == "CAT_add" || f_name == "CAT_sub")) 
        {
          auto v1 = cal_INst->getOperand(1), v2 = cal_INst->getOperand(2);
          unordered_set<ConstantInt*> const_num1, const_num2;
          int IN_count1 = 0, IN_count2 = 0;
          if(auto d1 = dyn_cast<CallInst>(v1)) 
          {
            BitVector IN1 = IN[cal_INst], d1_set = ssaVarCluster[ssaVarOrder[d1]];
            d1_set &= IN1;
            for(unsigned i = 0; i < ssaVarCnt; i++) 
            {
              if(d1_set[i] == 1) IN_count1++;
            }
            for(unsigned i  = 0; i < ssaVarCnt; i++) 
            {
              if(d1_set[i] == 1) {
                StringRef name = dyn_cast<CallInst>(OrderSsaVar[i])->getCalledFunction()->getName();
                if(name == "CAT_new" && isa<ConstantInt>(OrderSsaVar[i]->getOperand(0))) 
                {
                  const_num1.insert(cast<ConstantInt>(OrderSsaVar[i]->getOperand(0)));
                  IN_count1--;
                } 
                else if(name == "CAT_set" && isa<ConstantInt>(OrderSsaVar[i]->getOperand(1))) 
                {
                  const_num1.insert(cast<ConstantInt>(OrderSsaVar[i]->getOperand(1)));
                  IN_count1--;
                } 
              }
            }
          }
          if(auto d2 = dyn_cast<CallInst>(v2)) 
          {
            BitVector IN2 = IN[cal_INst], d2_set = ssaVarCluster[ssaVarOrder[d2]];
            d2_set &= IN2;
            for(unsigned i = 0; i < ssaVarCnt; i++) 
            {
              if(d2_set[i] == 1) IN_count2++;
            }
            for(unsigned i = 0; i < ssaVarCnt; i++) 
            {
              if(d2_set[i] == 1) {
                StringRef name = dyn_cast<CallInst>(OrderSsaVar[i])->getCalledFunction()->getName();
                if(name == "CAT_new" && isa<ConstantInt>(OrderSsaVar[i]->getOperand(0))) 
                {
                  const_num2.insert(cast<ConstantInt>(OrderSsaVar[i]->getOperand(0)));
                  IN_count2--;
                } 
                else if(name == "CAT_set" && isa<ConstantInt>(OrderSsaVar[i]->getOperand(1))) 
                {
                  const_num2.insert(cast<ConstantInt>(OrderSsaVar[i]->getOperand(1)));
                  IN_count2--;
                }
              }
            }            
          }
          if(const_num1.size() == 1 && const_num2.size() == 1 && IN_count1 == 0 && IN_count2 == 0)  
          {
              Value* result;
              IRBuilder<> builder(cal_INst);
              if(f_name == "CAT_add") 
              {
                result = builder.CreateAdd(*const_num1.begin(), *const_num2.begin());
              } 
              else 
              {
                result = builder.CreateSub(*const_num1.begin(), *const_num2.begin());
              }
              auto call = builder.CreateCall(F.getParent()->getFunction("CAT_set"), {
                cal_INst->getOperand(0),
                result
              });
              dyn_cast<CallInst>(call)->setTailCall();
              cal_INst->eraseFromParent();
          } 
          else if(v1 == v2 && f_name == "CAT_sub") 
          {
            Value *result =  ConstantInt::get(IntegerType::get(F.getParent()->getContext(), 64), 0);
            IRBuilder<> builder(cal_INst);
            auto call = builder.CreateCall(F.getParent()->getFunction("CAT_set"), {
                cal_INst->getOperand(0),
                result
            });
            dyn_cast<CallInst>(call)->setTailCall();
            cal_INst->eraseFromParent();
          } 
        }
        GENINAndOUT(F);
        //printINAndOUT(F);
        queue<PHINode*> phi_list;
        for(auto &INst : instructions(F)) 
        {
          if(auto phi_node = dyn_cast<PHINode>(&INst)) 
          {
            phi_list.push((phi_node));
          }
        }
        while(!phi_list.empty()) 
        {
          auto INst = phi_list.front();
          phi_list.pop();
          if(auto phi_node = dyn_cast<PHINode>(INst)) 
          {
            if(phi_node->getNumOperands() == 1 && isa<ConstantInt>(phi_node->getIncomingValue(0))) 
            {
              phi_node->setOperand(0, cast<ConstantInt>(phi_node->getIncomingValue(0)));
            } else if(phi_node->getNumOperands() == 1 && isa<CallInst>(phi_node->getIncomingValue(0))) 
            {
              auto cal = cast<CallInst>(phi_node->getIncomingValue(0));
              if(cal->getCalledFunction()->getName() == "CAT_new") 
              {
                //phi_node->replaceAllUsesWith(cal);// to be deleted, iterate all use and modify if IN_set has new
                BitVector phi_bit = BitVector(ssaVarCnt, 0);
                for(unsigned i  = 0; i < phi_node->getNumOperands(); i++) 
                {
                  if(isa<CallInst>(phi_node->getIncomingValue(i)))
                    phi_bit |= cluster[cast<CallInst>(phi_node->getIncomingValue(i))];
                }
                for(auto it = phi_node->user_begin(); it != phi_node->user_end(); it++)  
                {
                  BitVector IN_set = IN[dyn_cast<CallInst>(*it)];
                  IN_set &= phi_bit;
                  if(IN_set != BitVector(ssaVarCnt, 0)) {
                    errs()<<"change from:"<<*phi_node<<"to:"<<*cal<<"\n";
                    it->replaceUsesOfWith(phi_node, cal);
                  }
                  if(isa<PHINode>(*it)) {
                     errs()<<"change from:"<<*phi_node<<"to:"<<*cal<<"\n";
                    it->replaceUsesOfWith(phi_node, cal);
                  }
                }
              } 
            }
            
            unordered_set<ConstantInt*> result_set;
            unsigned cnt = 0;
            for(unsigned i = 0; i < phi_node->getNumOperands(); i++) 
            {
              if(auto cat_cal =dyn_cast<CallInst>(phi_node->getOperand(i))) 
              {
                if(cat_cal->getCalledFunction()->getName() == "CAT_new" && isa<ConstantInt>(cat_cal->getOperand(0))) 
                {
                  result_set.insert(cast<ConstantInt>(cat_cal->getOperand(0)));
                  cnt++;
                }
              }
            } 
            if(result_set.size() == 1 && cnt == phi_node->getNumOperands()) 
            {
              for(auto user = phi_node->user_begin(); user != phi_node->user_end(); user++) 
              {
                auto cat_cal = dyn_cast<CallInst>(*user);
                if(cat_cal && cat_cal->getCalledFunction()->getName() == "CAT_get") 
                {
                  BitVector IN_bit = IN[cat_cal], phi_bit = IN[phi_node];
                  if(IN_bit == phi_bit) 
                  {
                    vector<Value*> use_list;
                    for(auto u : user->users()) 
                    {
                      use_list.push_back(u);
                    }
                    for(auto u : use_list) 
                    {
                      dyn_cast<CallInst>(u)->setOperand(1, *result_set.begin());
                      del_list.insert(cast<CallInst>(cat_cal));
                    }
                  }
                }
              }
            }
          }
        }
      } while(!work_list.empty());
      for(auto i : del_list) 
      {
        i->eraseFromParent();
      }

    }
    void GENINAndOUT(Function &F) {
        OrderSsaVar.clear();
        ssaVarOrder.clear();
        ssaVarCluster.clear();
        cluster.clear();
        ssaVarCnt = 0;
        IN.clear();OUT.clear();GEN.clear();KILL.clear();
        for(auto &INst : instructions(F)) {
          if(isa<CallInst>(INst)) {
            CallInst &cal_INst = cast<CallInst>(INst);
            addLabel(&cal_INst);
          }
        }
        setBitVector();
        for(auto &INst : instructions(F)) {
          if(isa<CallInst>(INst)) {
            auto &cal_INst = cast<CallInst>(INst);
            setCluster(&cal_INst);
          }
        }
        setINAndOUT(F);
      }
    
    bool runOnFunction (Function &F) override {
      GENINAndOUT(F);
      optimizeFunction(F);
      return false;
    }
    void printBit(BitVector tmp)
    {
      for(uint i=0;i<tmp.size();++i)errs()<<tmp[i];
      errs()<<"\n";
    }
    void printINAndOUT(Function &F) 
    {
      for(auto &INst : instructions(F)) {
        auto IN_bit = IN[&INst]; 
        errs() << "Instruction: " << INst << "\n";
        errs() << "***************** IN\n{\n";
        for(unsigned i = 0; i < IN_bit.size(); i++) {
          if(IN_bit[i] == true) errs() << " " << *OrderSsaVar[i] << "\n";
        }
        errs() << "}\n**************************************\n";
        errs() << "***************** OUT\n{\n";
        auto OUT_bit = OUT[&INst];
        for(unsigned i = 0; i < OUT_bit.size(); i++) {
          if(OUT_bit[i] == true) errs() << " " << *OrderSsaVar[i] << "\n";
        }
        errs() << "}\n**************************************\n\n\n\n";
      }
    }
    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0