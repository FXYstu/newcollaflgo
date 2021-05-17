/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <vector>
#include <set>
#include <map>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <list>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/DenseSet.h>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CFGPrinter.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

using namespace llvm;
using namespace std;
using xyz = std::array<int, 3>;
using cur_pre = std::array<unsigned int, 2>;
set<unsigned int> hashes, tmpHashSet;
vector< BasicBlock *> singleBBS, multiBBS, solv, unsolv;
map<  BasicBlock*  ,  vector< BasicBlock* >> preds;
map<  BasicBlock*  , unsigned int> keys;
map<  BasicBlock*, xyz> params;
map<cur_pre, unsigned int> hashMap;
map<unsigned int, unsigned int> singleMap;
set<unsigned int> collmap;//record collision hash
int coll = 0;//collision
int all = 0;//allendge


cl::opt<std::string> DistanceFile(
    "distance",
    cl::desc("Distance file containing the distance of each basic block to the provided targets."),
    cl::value_desc("filename")
);

cl::opt<std::string> TargetsFile(
    "targets",
    cl::desc("Input file containing the target lines of code."),
    cl::value_desc("targets"));

cl::opt<std::string> OutDirectory(
    "outdir",
    cl::desc("Output directory where Ftargets.txt, Fnames.txt, and BBnames.txt are generated."),
    cl::value_desc("outdir"));

namespace llvm {

template<>
struct DOTGraphTraits<Function*> : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(Function *F) {
    return "CFG for '" + F->getName().str() + "' function";
  }

  std::string getNodeLabel(BasicBlock *Node, Function *Graph) {
    if (!Node->getName().empty()) {
      return Node->getName().str();
    }

    std::string Str;
    raw_string_ostream OS(Str);

    Node->printAsOperand(OS, false);
    return OS.str();
  }
};

} // namespace llvm
static bool disjoint(set<unsigned int>& hashes, set<unsigned int>& tmpHashSet)  {
  for (auto hash : hashes){
    for (auto tmpHash : tmpHashSet)
      if (hash == tmpHash)
        return false;
  }
  return true;

}
/* search parameters for blocks with multiple precedents */
/*static void calcFmul() {
  //sizeof(unsol) < delta or unsolv/BBSet  < sigma
  int delta =  10;
  double min = 1;
  double sigma = 0.001;
  int i = 1;
  for (int y = 1; y < MAP_SIZE_POW2; y++ ) {
    hashes.clear();
    params.clear();
    solv.clear();
    unsolv.clear();
    for (auto BB : multiBBS) {
      for (int x = 1; x < MAP_SIZE_POW2; x++ ) {
        for (int z = 1; z < MAP_SIZE_POW2; z++ ) {
          tmpHashSet.clear();
          auto cur = keys[BB];
          for (auto p : preds[BB]) {
            auto edgeHash = (cur >> x) ^ (keys[p] >> y) + z;
            tmpHashSet.insert(edgeHash);
          }
          if (tmpHashSet.size() == preds[BB].size() && disjoint(tmpHashSet, hashes)) {
            i++;
            solv.push_back(BB);
            params[BB] = xyz({x, y, z});
            hashes.insert(tmpHashSet.begin(), tmpHashSet.end());
          }
        }
      }

      unsolv.push_back(BB);
    }
    auto sizeofUnsolv = unsolv.size();
    auto sizeofSolv = solv.size();
    auto _min = (double)sizeofUnsolv / (sizeofUnsolv + sizeofSolv);
    if (_min < min) min = _min;
    if(sizeofUnsolv < delta || _min < sigma) {
      errs() << "I'm going to break. " << '\n';
      break;
    }

  }
  //errs() << "min：" <<　min << '\n';
  //errs() << "i: " << i << '\n';
}*/

static void calcFmul() {
  //sizeof(unsol) < delta or unsolv/BBSet  < sigma
  int delta =  10;
  double min = 1;
  double sigma = 0.001;
  int i = 1;

  for (int y = 1; y < MAP_SIZE_POW2; y++ ) {
    //make set or map to empty
    hashes.clear();
    params.clear();
    solv.clear();
    unsolv.clear();
    for (auto BB : multiBBS) {
      int flag = 0;
      // search parameters for BB
      for (int x = 1; x < MAP_SIZE_POW2; x++ ) {
        for (int z = 1; z < MAP_SIZE_POW2; z++ ) {
          tmpHashSet.clear();
          auto cur = keys[BB];
          // hashes for all incoming edges
          for (auto p : preds[BB]) {
            auto edgeHash = (cur >> x) ^ (keys[p] >> y) + z;
            tmpHashSet.insert(edgeHash);
          }
          // find a solution for BB if no collision
          if (tmpHashSet.size() == preds[BB].size() && disjoint(tmpHashSet, hashes)) {
            i++;
            solv.push_back(BB);
            params[BB] = xyz({x, y, z});
            hashes.insert(tmpHashSet.begin(), tmpHashSet.end());
            flag=1;
            break;
          }
        }
        if (flag==1)
        {
             break;
        }

      }
      if (flag==1)
      {
          continue;
      }
      else
      {
           unsolv.push_back(BB);
      }

      //unsolv.push_back(BB);
    }
    auto sizeofUnsolv = unsolv.size();
    auto sizeofSolv = solv.size();
    auto _min = (double)sizeofUnsolv / (sizeofUnsolv + sizeofSolv);
    if (_min < min) min = _min;
    if(sizeofUnsolv < delta || _min < sigma) {
      errs() << "I'm going to break. " << '\n';
      //hashesmap.insert(tmpHashSet.begin(), tmpHashSet.end());
      break;
    }
  }
  //errs() << "min：" <<　min << '\n';
  //errs() << "i: " << i << '\n';
}

/* build the hash table for unsolvable blocksUnsol */

static void calcFhash() {
  hashMap.clear();
  for (auto BB : unsolv) {

    auto cur = keys[BB];
    for (auto p : preds[BB]) {

      auto pre = keys[p];
      for (int i = 0; i < MAP_SIZE; i++) {
        //errs() << hashes.size() << '\n';
        if (!hashes.count(i)) {
          hashMap[cur_pre({cur, pre})] = i;
          hashes.insert(i);
          break;
        }
      }

    }
  }
}

/* build the hash table for blocks with single precedent */

static void calcSingle() {
  singleMap.clear();
  for (auto BB : singleBBS) {

    auto cur = keys[BB];
      for (int i = 0; i < MAP_SIZE; i++) {

        if (!hashes.count(i)) {

          singleMap[cur] = i;
          hashes.insert(i);
          break;
        }
      }

  }
}

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}

char AFLCoverage::ID = 0;

static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) {
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}

static bool isBlacklisted(const Function *F) {
  static const SmallVector<std::string, 8> Blacklist = {
    "asan.",
    "llvm.",
    "sancov.",
    "__ubsan_handle_",
    "free",
    "malloc",
    "calloc",
    "realloc"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (F->getName().startswith(BlacklistFunc)) {
      return true;
    }
  }

  return false;
}

bool AFLCoverage::runOnModule(Module &M) {

  bool is_aflgo = false;
  bool is_aflgo_preprocessing = false;

  if (!TargetsFile.empty() && !DistanceFile.empty()) {
    FATAL("Cannot specify both '-targets' and '-distance'!");
    return false;
  }

  std::list<std::string> targets;
  std::map<std::string, int> bb_to_dis;
  std::vector<std::string> basic_blocks;

  if (!TargetsFile.empty()) {

    if (OutDirectory.empty()) {
      FATAL("Provide output directory '-outdir <directory>'");
      return false;
    }

    std::ifstream targetsfile(TargetsFile);
    std::string line;
    while (std::getline(targetsfile, line))
      targets.push_back(line);
    targetsfile.close();

    is_aflgo_preprocessing = true;

  } else if (!DistanceFile.empty()) {

    std::ifstream cf(DistanceFile);
    if (cf.is_open()) {

      std::string line;
      while (getline(cf, line)) {

        std::size_t pos = line.find(",");
        std::string bb_name = line.substr(0, pos);
        int bb_dis = (int) (100.0 * atof(line.substr(pos + 1, line.length()).c_str()));

        bb_to_dis.emplace(bb_name, bb_dis);
        basic_blocks.push_back(bb_name);

      }
      cf.close();

      is_aflgo = true;

    } else {
      FATAL("Unable to find %s.", DistanceFile.c_str());
      return false;
    }

  }

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    if (is_aflgo || is_aflgo_preprocessing)
      SAYF(cCYA "aflgo-llvm-pass (yeah!) " cBRI VERSION cRST " (%s mode)\n",
           (is_aflgo_preprocessing ? "preprocessing" : "distance instrumentation"));
    else
      SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");


  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Default: Not selective */
  char* is_selective_str = getenv("AFLGO_SELECTIVE");
  unsigned int is_selective = 0;

  if (is_selective_str && sscanf(is_selective_str, "%u", &is_selective) != 1)
    FATAL("Bad value of AFLGO_SELECTIVE (must be 0 or 1)");

  char* dinst_ratio_str = getenv("AFLGO_INST_RATIO");
  unsigned int dinst_ratio = 100;

  if (dinst_ratio_str) {

    if (sscanf(dinst_ratio_str, "%u", &dinst_ratio) != 1 || !dinst_ratio ||
        dinst_ratio > 100)
      FATAL("Bad value of AFLGO_INST_RATIO (must be between 1 and 100)");

  }

  /* Instrument all the things! */

  int inst_blocks = 0;

  if (is_aflgo_preprocessing) {

    std::ofstream bbnames(OutDirectory + "/BBnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream bbcalls(OutDirectory + "/BBcalls.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream fnames(OutDirectory + "/Fnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream ftargets(OutDirectory + "/Ftargets.txt", std::ofstream::out | std::ofstream::app);

    /* Create dot-files directory */
    std::string dotfiles(OutDirectory + "/dot-files");
    if (sys::fs::create_directory(dotfiles)) {
      FATAL("Could not create directory %s.", dotfiles.c_str());
    }

    for (auto &F : M) {

      bool has_BBs = false;
      std::string funcName = F.getName().str();

      /* Black list of function names */
      if (isBlacklisted(&F)) {
        continue;
      }

      bool is_target = false;
      for (auto &BB : F) {

        std::string bb_name("");
        std::string filename;
        unsigned line;

        for (auto &I : BB) {
          getDebugLoc(&I, filename, line);

          /* Don't worry about external libs */
          static const std::string Xlibs("/usr/");
          if (filename.empty() || line == 0 || !filename.compare(0, Xlibs.size(), Xlibs))
            continue;

          if (bb_name.empty()) {

            std::size_t found = filename.find_last_of("/\\");
            if (found != std::string::npos)
              filename = filename.substr(found + 1);

            bb_name = filename + ":" + std::to_string(line);
          }

          if (!is_target) {
              for (auto &target : targets) {
                std::size_t found = target.find_last_of("/\\");
                if (found != std::string::npos)
                  target = target.substr(found + 1);

                std::size_t pos = target.find_last_of(":");
                std::string target_file = target.substr(0, pos);
                unsigned int target_line = atoi(target.substr(pos + 1).c_str());

                if (!target_file.compare(filename) && target_line == line)
                  is_target = true;

              }
            }

            if (auto *c = dyn_cast<CallInst>(&I)) {

              std::size_t found = filename.find_last_of("/\\");
              if (found != std::string::npos)
                filename = filename.substr(found + 1);

              if (auto *CalledF = c->getCalledFunction()) {
                if (!isBlacklisted(CalledF))
                  bbcalls << bb_name << "," << CalledF->getName().str() << "\n";
              }
            }
        }

        if (!bb_name.empty()) {

          BB.setName(bb_name + ":");
          if (!BB.hasName()) {
            std::string newname = bb_name + ":";
            Twine t(newname);
            SmallString<256> NameData;
            StringRef NameRef = t.toStringRef(NameData);
            MallocAllocator Allocator;
            BB.setValueName(ValueName::Create(NameRef, Allocator));
          }

          bbnames << BB.getName().str() << "\n";
          has_BBs = true;

#ifdef AFLGO_TRACING
          auto *TI = BB.getTerminator();
          IRBuilder<> Builder(TI);

          Value *bbnameVal = Builder.CreateGlobalStringPtr(bb_name);
          Type *Args[] = {
              Type::getInt8PtrTy(M.getContext()) //uint8_t* bb_name
          };
          FunctionType *FTy = FunctionType::get(Type::getVoidTy(M.getContext()), Args, false);
          Constant *instrumented = M.getOrInsertFunction("llvm_profiling_call", FTy);
          Builder.CreateCall(instrumented, {bbnameVal});
#endif

        }
      }

      if (has_BBs) {
        /* Print CFG */
        std::string cfgFileName = dotfiles + "/cfg." + funcName + ".dot";
        std::error_code EC;
        raw_fd_ostream cfgFile(cfgFileName, EC, sys::fs::F_None);
        if (!EC) {
          WriteGraph(cfgFile, &F, true);
        }

        if (is_target)
          ftargets << F.getName().str() << "\n";
        fnames << F.getName().str() << "\n";
      }
    }

  } else {
    /* Distance instrumentation */

    LLVMContext &C = M.getContext();
    IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
    IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
    IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

#ifdef __x86_64__
    IntegerType *LargestType = Int64Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8);
#else
    IntegerType *LargestType = Int32Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 4);
#endif
    ConstantInt *MapDistLoc = ConstantInt::get(LargestType, MAP_SIZE);
    ConstantInt *One = ConstantInt::get(LargestType, 1);

    /* Get globals for the SHM region and the previous location. Note that
       __afl_prev_loc is thread-local. */

    GlobalVariable *AFLMapPtr =
        new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                           GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

    GlobalVariable *AFLPrevLoc = new GlobalVariable(
        M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
        0, GlobalVariable::GeneralDynamicTLSModel, 0, false);
  /* Instrument all the things! */

    //int inst_blocks = 0;
    int i = 1;
    for (auto &F : M){
      for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      //BasicBlock* BB = b;

        i++;
        BasicBlock* BB = &*b;
        //TerminatorInst *TInst = BB->getTerminator();
        unsigned NSucc = BB->getTerminator()->getNumSuccessors();
        if(NSucc == 1) {
          //errs() << "single" << '\n';
          singleBBS.push_back(BB);
        }
        else if(NSucc > 1) {
          //errs() << "multiple" << '\n';
          multiBBS.push_back(BB);

          }
          for (unsigned I = 0; I < NSucc; ++I) {
            BasicBlock *Succ = BB->getTerminator()->getSuccessor(I);
            preds[BB].push_back(Succ);
        }
        if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

        unsigned int cur_loc = AFL_R(MAP_SIZE);
        keys[BB] = cur_loc;
      }
    }
    errs() << "singleBSS size: " << singleBBS.size() << '\n';
    errs() << "multiBSS size: " << multiBBS.size() << '\n';
    // calc hashes for blocks
    calcFmul();
    calcFhash();
    calcSingle();
    errs() << "solv size: " << solv.size() << '\n';
    errs() << "unsolv size: " << unsolv.size() << '\n';
   // errs() << "singleMap size: " << singleMap.size() << '\n';
    //errs() << "hashMap size: " << hashMap.size() << '\n';
    //errs() << "keys size: " << keys.size() << '\n';
    //errs() << "params size: " << params.size() << '\n';
    //errs() << "preds size: " << preds.size() << '\n';

    for (auto &F : M) {

      int distance = -1;
      for (auto &BB : F) {
        BasicBlock* Bb=&BB;//coll_fast

        distance = -1;

        if (is_aflgo) {

          std::string bb_name;
          for (auto &I : BB) {
            std::string filename;
            unsigned line;
            getDebugLoc(&I, filename, line);

            if (filename.empty() || line == 0)
              continue;
            std::size_t found = filename.find_last_of("/\\");
            if (found != std::string::npos)
              filename = filename.substr(found + 1);

            bb_name = filename + ":" + std::to_string(line);
            break;
          }

          if (!bb_name.empty()) {

            if (find(basic_blocks.begin(), basic_blocks.end(), bb_name) == basic_blocks.end()) {

              if (is_selective)
                continue;

            } else {

              /* Find distance for BB */

              if (AFL_R(100) < dinst_ratio) {
                std::map<std::string,int>::iterator it;
                for (it = bb_to_dis.begin(); it != bb_to_dis.end(); ++it)
                  if (it->first.compare(bb_name) == 0)
                    distance = it->second;

              }
            }
          }
        }
        BasicBlock::iterator IP = BB.getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));
        if (AFL_R(100) >= inst_ratio) continue;
        if (!keys.count(Bb)) {
          errs() << "BB not in keys" << '\n';
          continue;
        }
        auto cur_loc = keys[Bb];
        LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
        PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        // BBS with one precedent
        int X = 0;
        int Y = 1;
        int Z = 1;
        LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
        MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());
        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc >> X);
        Value *MapPtrIdx =
            IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

        if (singleMap.count(cur_loc)) {
          ConstantInt *CurLoc = ConstantInt::get(Int32Ty, singleMap[cur_loc]);
          Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, CurLoc);
          //errs() << "singleMap.count(cur_loc) " << *CurLoc << " MapPtrIdx: "　<< *MapPtrIdx << '\n';
        }
        else if (params.count(Bb)) {

           auto XYZ = params[Bb];

          X = XYZ[0];
          Y = XYZ[1];
          Z = XYZ[2];
          //errs() << "X: " << X << " Y: " << Y << " Z: " << Z << '\n';
          ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc >> X);

       /* Load prev_loc */

          auto XorCurPre = IRB.CreateXor(PrevLocCasted, CurLoc);
          auto XorPlusZ = IRB.CreateAdd(XorCurPre, ConstantInt::get(Int32Ty, Z));
          Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, XorPlusZ);
          //errs() << "params.count(BB): " << *XorPlusZ << " MapPtrIdx: " << *MapPtrIdx  << '\n';
        }
        else {

            //auto pre = (unsigned int)dyn_cast<ConstantInt>((AFLPrevLoc)->getValue());
            // Value* loadedValue = new LoadInst(AFLPrevLoc);
            // auto pre = *ExecutionEngine::getGlobalValueAtAddress(AFLPrevLoc);

            // if (hashMap.count(cur_pre({cur_loc, pre}))) {
            //   ConstantInt *CurLoc = ConstantInt::get(Int32Ty, hashMap[cur_pre{cur_loc, pre}]);
            //   Value *MapPtrIdx =
            //   IRB.CreateGEP(MapPtr, CurLoc);
            //   errs() << "else: " << *CurLoc << " MapPtrIdx: " << *MapPtrIdx  << '\n';
            // }

        }
        /* Update bitmap */

        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
        IRB.CreateStore(Incr, MapPtrIdx)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        /* Set prev_loc to cur_loc >> Y */

        StoreInst *Store =
            IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> Y), AFLPrevLoc);
        Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        if (distance >= 0) {

          ConstantInt *Distance =
              ConstantInt::get(LargestType, (unsigned) distance);

          /* Add distance to shm[MAPSIZE] */

          Value *MapDistPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapDistLoc), LargestType->getPointerTo());
          LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
          MapDist->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          Value *IncrDist = IRB.CreateAdd(MapDist, Distance);
          IRB.CreateStore(IncrDist, MapDistPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          /* Increase count at shm[MAPSIZE + (4 or 8)] */

          Value *MapCntPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo());
          LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
          MapCnt->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
          IRB.CreateStore(IncrCnt, MapCntPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        }
         inst_blocks++;
      }
    }
  }
  /* Say something nice. */

  if (!is_aflgo_preprocessing && !be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%, dist. ratio %u%%).",
             inst_blocks,
             getenv("AFL_HARDEN")
             ? "hardened"
             : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
               ? "ASAN/MSAN" : "non-hardened"),
             inst_ratio, dinst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());
  PassManagerBuilder *builder = new PassManagerBuilder();
  // builder.VerifyInput = true;
  builder->populateLTOPassManager(PM);

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
