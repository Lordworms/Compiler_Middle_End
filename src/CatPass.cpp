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
using uit=unsigned int;
namespace {
  struct CAT : public FunctionPass {
    static char ID; 
    Module *currentModule;
    int ssaVarCnt=0;//number of all ssa variable
    unordered_map<Instruction*,int>ssaVarOrder;//order of each ssa variable
    unordered_map<int,Instruction*>orderSsaVar;//use index to trace ssa variable
    unordered_map<Instruction*,BitVector>IN,OUT,GEN,KILL;//four set of a instruction
    unordered_map<Instruction*,BitVector>cluster;//get all ssa variable assotiated with this instruction
    unordered_map<int,BitVector>ssaVarOrderCluster;//use order to trace cluster
    set<StringRef>catFuncName;//store all names
    CAT() : FunctionPass(ID) {}
    bool doInitialization (Module &M) override {
      currentModule = &M;
      catFuncName.insert("CAT_new");
      catFuncName.insert("CAT_set");
      catFuncName.insert("CAT_add");
      catFuncName.insert("CAT_sub"); 
      return false;
    }
    void doClear()//clear all sets
    {
      ssaVarOrder.clear();
      ssaVarOrderCluster.clear();
      orderSsaVar.clear();
      IN.clear();OUT.clear();KILL.clear();GEN.clear();
      cluster.clear();
      ssaVarCnt=0;
    }
    void addVar(Instruction* I)
    {
        ssaVarOrder[I]=ssaVarCnt;
        orderSsaVar[ssaVarCnt]=I;
        ++ssaVarCnt;
    }
    void initBit(Function& F)
    {
      for(auto &[I,order]:ssaVarOrder)
      {
        BitVector tmp(ssaVarCnt,false);
        tmp[order]=true;
        cluster[I]=tmp;
      }
    }
    void getCluster(CallInst* inst)//get ssa variable for non-ssa variable
    {
        StringRef funcName=inst->getCalledFunction()->getName();
        if(funcName=="CAT_new")
        {
          ssaVarOrderCluster[ssaVarOrder[inst]]|=cluster[inst];//add this to its cluster
        }
        else if(catFuncName.count(funcName))
        {
          auto op0=inst->getArgOperand(0);
          if(isa<PHINode>(op0))//if it is a phinode, we need to set this instuction with its variable
          {
            auto opPhi0=cast<PHINode>(op0);
            for(uit i=0;i<opPhi0->getNumOperands();++i)
            {
              if(isa<CallInst>(opPhi0->getOperand(i)))
              {
                auto phiI=cast<CallInst>(opPhi0->getOperand(i));
                ssaVarOrderCluster[ssaVarOrder[phiI]]|=cluster[inst];
              }
            }
          }
          else if(isa<CallInst>(op0)&&cast<CallInst>(op0)->getCalledFunction()->getName()=="CAT_new")//every variable is defined
              {
                auto var0=cast<Instruction>(inst->getOperand(0));
                ssaVarOrderCluster[ssaVarOrder[var0]]|=cluster[inst];
              }
        }
    }
    void genKillAndGen(Instruction* ins)//gen = cluster[i]
    {
      StringRef funcName;
      BitVector kill(ssaVarCnt,false);
      if(isa<CallInst>(ins))funcName=cast<CallInst>(ins)->getCalledFunction()->getName();
      if(funcName=="CAT_new")//genset is itsself
      {
        kill=ssaVarOrderCluster[ssaVarOrder[ins]];
        GEN[ins]=cluster[ins];
      }
      else if(catFuncName.count(funcName))
      {
        auto op0=ins->getOperand(0);
        GEN[ins]=cluster[ins];
        if(isa<PHINode>(op0))
        {
          kill|=cluster[ins];//kill set contains itself
        }
        else if(isa<CallInst>(ins->getOperand(0)))
        {
          CallInst* inst=cast<CallInst>(ins->getOperand(0));
          kill=ssaVarOrderCluster[ssaVarOrder[inst]];
        }
      }
      else
      {
        GEN[ins]=BitVector(ssaVarCnt,false);
      }
      if(catFuncName.count(funcName))
      {
        kill^=cluster[ins];
        KILL[ins]=kill;
      }
      else
      {
        KILL[ins]=BitVector(ssaVarCnt,false);
      }
    }
    void genInAndOut(Function* F)
    {
      queue<Instruction*>q;
      for(Instruction& I:instructions(F))q.push(&I);
      while(!q.empty())
      {
        auto tmp=q.front();
        q.pop();
        auto pa=tmp->getParent();
        BitVector in(ssaVarCnt,false),out(ssaVarCnt,false),kill=KILL[tmp],gen=GEN[tmp];
        auto oldOut=OUT[tmp];
        if(&pa->front()==tmp)//it is the first instruction
        {
          for(auto pre:predecessors(pa))
          {
            in|=OUT[pre->getTerminator()];
          }
        }
        else 
        {
          in|=OUT[tmp->getPrevNode()];
        }
        out|=in;
        out|=gen;
        out&=kill.flip();
        IN[tmp]=in;
        OUT[tmp]=out;
        if(OUT[tmp]!=oldOut)
        {
          if(tmp==pa->getTerminator())
          {
            for(auto nxt:successors(pa))q.push(&nxt->front());
          }
          else
          {
            q.push(tmp->getNextNode());
          }
        }
      }
    }
    void initSet(Function& F)//this function is used to generate IN,OUT,GEN,KILL
    {
      doClear();
      for(auto& I:instructions(&F))
      {
        if(isa<CallInst>(I))
        {
          CallInst& inst=cast<CallInst>(I);
          addVar(&inst);
        }
      }
      initBit(F);
      int t=0;
      for(auto &I:instructions(&F))
      {
        if(isa<CallInst>(I))
        { 
          if(CallInst* inst=cast<CallInst>(&I))
          {
            ++t;
            getCluster(inst);
          }
        }
      }
      for(auto& I:instructions(&F))genKillAndGen(&I);
      genInAndOut(&F);
    }
    void constantOptimization(Function &F)
    {
      queue<CallInst*>q;
      for(auto& I:instructions(F))
      {
        if(auto inst=dyn_cast<CallInst>(&I))
        {
          q.push(inst);
        }
      }
      while(!q.empty())
      {
        auto tmp=q.front();
        q.pop();
        auto funcName=tmp->getCalledFunction()->getName();
        if(funcName=="CAT_get"&&isa<CallInst>(tmp->getArgOperand(0)))
        { 
          auto op0=tmp->getArgOperand(0);
          auto op0Ins=dyn_cast<CallInst>(op0);
          auto getSet=IN[tmp];
          getSet&=ssaVarOrderCluster[ssaVarOrder[op0Ins]];
          int varCnt=getCnt(getSet);
          unordered_set<ConstantInt*>resSet;
          for(uit i=0;i<getSet.size();++i)
          {
            if(getSet[i]==false)continue;
            auto varName=dyn_cast<CallInst>(orderSsaVar[i])->getCalledFunction()->getName();
            ConstantInt* value=nullptr;
            if(varName=="CAT_new")
            {
                if(auto res=dyn_cast<ConstantInt>(orderSsaVar[i]->getOperand(0)))
                {
                  value=res;
                }
            }
            else if(varName=="CAT_set")
            {
                if(auto res=dyn_cast<ConstantInt>(orderSsaVar[i]->getOperand(1)))
                {
                  errs()<<*tmp<<"\n";
                  value=res;
                }
            }
            else if(varName=="CAT_add"||varName=="CAT_sub")
            {
              auto op1=orderSsaVar[i]->getOperand(1);
              auto op2=orderSsaVar[i]->getOperand(2);
              if(isa<ConstantInt>(op1)&&isa<ConstantInt>(op2))
              {
                auto v1=cast<ConstantInt>(op1)->getSExtValue();
                auto v2=cast<ConstantInt>(op2)->getSExtValue();
                value=ConstantInt::get(IntegerType::get(F.getParent()->getContext(),32),varName=="CAT_add"?v1+v2:v1-v2);
              }
            }
            if(value)
            {
              resSet.insert(value);
              --varCnt;
            }
          }
          if(varCnt==0&&resSet.size()==1)
          {
            errs()<<**resSet.begin()<<"to "<<*tmp<<"\n";
            tmp->replaceAllUsesWith(*resSet.begin());
            tmp->eraseFromParent();
          }
        }
        //do constant folding
        else if(funcName=="CAT_add"||funcName=="CAT_sub")
        {
            auto op1=tmp->getOperand(1),op2=tmp->getOperand(2);
            unordered_set<ConstantInt*>st1,st2;
            int varCnt1=0,varCnt2=0;
            if(CallInst* v1=dyn_cast<CallInst>(op1))
            { 
              auto getSet=IN[tmp];
              getSet&=ssaVarOrderCluster[ssaVarOrder[v1]];
              errs()<<"bits of v1:"<<"\n";
              printBit(getSet);
              varCnt1=getCnt(getSet);
              for(uit i=0;i<getSet.size();++i)
              {
                if(getSet[i]==false)continue;
                auto varName=dyn_cast<CallInst>(orderSsaVar[i])->getCalledFunction()->getName();
                if(varName=="CAT_new"&&isa<ConstantInt>(orderSsaVar[i]->getOperand(0)))
                {
                  st1.insert(cast<ConstantInt>(orderSsaVar[i]->getOperand(0)));
                  --varCnt1;
                }
                else if(varName=="CAT_set"&&isa<ConstantInt>(orderSsaVar[i]->getOperand(1)))
                {
                   st1.insert(cast<ConstantInt>(orderSsaVar[i]->getOperand(1)));
                   --varCnt1;
                }
              }
            }
            if(CallInst* v2=dyn_cast<CallInst>(op2))
            {
              auto getSet=IN[tmp];
              getSet&=ssaVarOrderCluster[ssaVarOrder[v2]];
              errs()<<"bits of v2:"<<"\n";
              printBit(getSet);
              varCnt2=getCnt(getSet);
              for(uit i=0;i<getSet.size();++i)
              {
                if(getSet[i]==false)continue;
                auto varName=dyn_cast<CallInst>(orderSsaVar[i])->getCalledFunction()->getName();
                if(varName=="CAT_new"&&isa<ConstantInt>(orderSsaVar[i]->getOperand(0)))
                {
                  st2.insert(cast<ConstantInt>(orderSsaVar[i]->getOperand(0)));
                  --varCnt2;
                }
                else if(varName=="CAT_set"&&isa<ConstantInt>(orderSsaVar[i]->getOperand(1)))
                {
                   st2.insert(cast<ConstantInt>(orderSsaVar[i]->getOperand(1)));
                   --varCnt2;
                }
              }
            }
            errs()<<st1.size()<<" "<<st2.size()<<" "<<varCnt1<<" "<<varCnt2<<"\n";
            if(st1.size()==1&&st2.size()==1&&varCnt1==0&&varCnt2==0)
            {
                
                IRBuilder<>builder(tmp);
                auto v1=*st1.begin(),v2=*st2.begin();
                auto res=funcName=="CAT_add"?builder.CreateAdd(v1,v2):builder.CreateSub(v1,v2);
                auto call=builder.CreateCall(F.getParent()->getFunction("CAT_set"),{
                  tmp->getOperand(0),
                  res
                });
                errs()<<*call<<"\n";
                call->setTailCall();
                tmp->eraseFromParent();
            }
            else if(op1==op2&&funcName=="CAT_sub")
            { 
              auto res=ConstantInt::get(IntegerType::get(F.getParent()->getContext(),64),0);
              IRBuilder<>builder(tmp);
              auto call=builder.CreateCall(F.getParent()->getFunction("CAT_set"),{
                  tmp->getOperand(0),
                  res
                });
              call->setTailCall();
              tmp->eraseFromParent();
            }
        }
        initSet(F);
      }
    }
    bool runOnFunction (Function &F) override {
      initSet(F);
      constantOptimization(F);
      return false;
    }
    void printInAndOut(Function &F) {
        for(auto &ins: instructions(F)) {
        auto in = IN[&ins]; 
        errs() << "INSTRUCTION: " << ins << "\n";
        errs() << "***************** IN\n{\n";
        for(unsigned i = 0; i < in.size(); i++) {
          if(in[i] == true) errs() << " " << *orderSsaVar[i] << "\n";
        }
        errs() << "}\n**************************************\n";
        errs() << "***************** OUT\n{\n";
        auto out = OUT[&ins];
        for(unsigned i = 0; i < out.size(); i++) {
          if(out[i] == true) errs() << " " << *orderSsaVar[i] << "\n";
        }
        errs() << "}\n**************************************\n\n\n\n";
        }
    }
    int getCnt(BitVector& tmp)
    {
      int cnt=0;
      for(uit i=0;i<tmp.size();++i)if(tmp[i])++cnt;
      return cnt;
    }
    void printBit(BitVector tmp)
    {
      for(uit i=0;i<tmp.size();++i)errs()<<tmp[i];
      errs()<<"\n";
    }
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
