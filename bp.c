/* 046267 Computer Architecture - Winter 20/21 - HW #1                  */
/* This file should hold your implementation of the predictor simulator */

#include "bp_api.h"
#include <math.h>
#include <stdlib.h>

#define MAX_PC 0x7FFFFFFF
#define DEFAULT_TARGET 0x0
#define NO_HISTORY_YET 0X0


//useful typedefs for return types, state machines, and decisions
typedef enum { SNT = 0, WNT = 1, WT = 2, ST = 3 } Bstate;
typedef enum { INCREMENT = 1, DECREMENT = 0} StateDirection;
typedef enum { NOT_TAKEN = false, TAKEN = true, NOT_EXIST = false } Decision;
typedef enum { ALLOCATION_ERR = -2, FAIL = -1, SUCCESS = 0 } ReturnCode;
typedef enum { NO_SHARE = 0, LSB = 1, MID = 2 } ShareType;

//helping functions
static Bstate stateIncrement(Bstate state, StateDirection direction){
    state = direction ? (state == ST ? state : state + 1) : (state == SNT ? state : state - 1);
    return state;
}

static unsigned int calcTotalSize(unsigned int btbSize,unsigned int historySize,unsigned int tagSize,bool isGlobalHist,bool isGlobalTable){
    int valid_bit_size = 1, adress_size = 30;
    unsigned int total_size = btbSize*(valid_bit_size + tagSize + adress_size);
    total_size += isGlobalHist ? historySize : (btbSize*historySize);
    total_size += isGlobalTable ? (2*(int)pow(2,historySize)) : (2*btbSize*(int)pow(2,historySize));
    return total_size;
}

static uint8_t calcHistMask(unsigned int histSize){
    //this function deals with a 8 bit history register.
    uint8_t mask = 0x0;
    for(int i = (int)histSize - 1 ; i >=0 ; i--){
        mask += (uint8_t)pow(2,i);
    }
    return mask;
}

static uint32_t calcBtbIdxMask(unsigned int btbSize){
    //this function deals with a 32 bit address.
    int idxSize = (int)log2(btbSize);
    uint32_t mask = 0x0;
    for(int i = idxSize - 1 ; i >= 0 ; i--){
        mask += (uint8_t)pow(2,i);
    }
    mask *= 4;
    return mask;
}

static uint32_t calcTagMask(unsigned int tagSize, unsigned int btbSize){
    //this function deals with a 32 bit address.
    int idxSize = (int)log2(btbSize);
    uint32_t mask = 0x0;
    for(int i = (int)tagSize - 1  ; i >= 0 ; i--){
        mask += (uint32_t)pow(2,i);
    }
    mask *= 4;
    mask *= (uint32_t)pow(2,idxSize);
    return mask;
}

//main structs: branch op, and the global simulator struct
typedef struct branch_t{
    uint32_t tag;
    uint32_t target;
    uint8_t local_history_reg;
    Bstate* local_pred_machine;
} Branch;

typedef struct simulator{
    SIM_stats simulator_stats;
    unsigned int btbSize;
    unsigned int histSize;
    unsigned int tagSize;
    ShareType share_type;
    bool global_his;
    bool global_pred_table;
    Bstate default_state;
    uint8_t global_his_reg;
    Bstate* global_pred_machine;
}Sim;

static Branch* BTB = NULL;

static Sim sim;

static void free_everything() {
    //delete all the allocated fucks.
    if(sim.global_pred_table){
        free(sim.global_pred_machine);
    } else {
        for(unsigned int i = 0 ; i < sim.btbSize ; i++){
            if(BTB[i].local_pred_machine){
                free(BTB[i].local_pred_machine);
            }
        }
    }
    free(BTB);
}

int BP_init(unsigned btbSize, unsigned historySize, unsigned tagSize, unsigned fsmState,
            bool isGlobalHist, bool isGlobalTable, int Shared){
    sim.btbSize = btbSize;
    sim.histSize = historySize;
    sim.tagSize = tagSize;
    sim.default_state = fsmState;
    sim.global_his = isGlobalHist;
    sim.global_pred_table = isGlobalTable;
    sim.share_type = Shared;
    sim.simulator_stats.br_num = 0;
    sim.simulator_stats.flush_num = 0;
    sim.simulator_stats.size = calcTotalSize(btbSize,historySize,tagSize,isGlobalHist,isGlobalTable);
    sim.global_his_reg = NO_HISTORY_YET;
    if(isGlobalTable) {
        sim.global_pred_machine = malloc((int) pow(2, historySize) * sizeof(Bstate));
        if (!sim.global_pred_machine) {
            return FAIL;
        }
        for(int i = 0 ; i < (int) pow(2, historySize) ; i++){
            sim.global_pred_machine[i] = fsmState;
        }
    }
    BTB = malloc(btbSize*sizeof(Branch));
    if(!BTB){
        free(sim.global_pred_machine);
        return FAIL;
    }
    for(unsigned int i = 0 ; i < btbSize ; i++){
        BTB[i].tag = MAX_PC;
        BTB[i].target = DEFAULT_TARGET;
        BTB[i].local_history_reg = NO_HISTORY_YET;
        BTB[i].local_pred_machine = NULL;
    }
    return SUCCESS;
}

bool BP_predict(uint32_t pc, uint32_t *dst){
    //first, check if the branch exists
    uint32_t pcIdx = pc & calcBtbIdxMask(sim.btbSize), pcTag = pc & calcTagMask(sim.tagSize,sim.btbSize);
    pcIdx /= (uint32_t)4;
    pcTag /= (uint32_t)4;
    if(BTB[pcIdx].target == DEFAULT_TARGET || BTB[pcIdx].tag != pcTag){
        *dst = pc + (uint32_t)4;
        return NOT_EXIST;
    }
    //now that it exists, go to the state machine by the index for the history reg,
    // and figure out whats it's state.
    uint32_t pcHistIdx = sim.global_his ? sim.global_his_reg & calcHistMask(sim.histSize) :
                         BTB[pcIdx].local_history_reg & calcHistMask(sim.histSize);
    Bstate pcState;
    if(sim.global_pred_table){
        if(sim.share_type == LSB){
            uint32_t pcLSB = pc &(calcHistMask(sim.histSize)*(uint32_t)4);
            pcLSB /= (uint32_t)4;
            pcHistIdx ^= pcLSB;
        }
        if(sim.share_type == MID){
            uint32_t pcMID = pc & (calcHistMask(sim.histSize)*(uint32_t)pow(2,16));
            //the next line is suspecious, it might be >> 4
            pcMID /= (uint32_t)(pow(2,16));
            pcHistIdx ^= pcMID;
        }
        pcState = sim.global_pred_machine[pcHistIdx];
    } else {
        pcState = BTB[pcIdx].local_pred_machine[pcHistIdx];
    }
    switch (pcState) {
        case WNT:
        case SNT:
            *dst = pc + (uint32_t)4;
            return NOT_TAKEN;
        case WT:
        case ST:
            *dst = BTB[pcIdx].target;
            return TAKEN;
        default:
            break;
    }
    return TAKEN;
}

void BP_update(uint32_t pc, uint32_t targetPc, bool taken, uint32_t pred_dst){
    uint32_t pcIdx = pc & calcBtbIdxMask(sim.btbSize), pcTag = pc & calcTagMask(sim.tagSize,sim.btbSize);
    pcIdx /= (uint32_t)4;
    pcTag /= (uint32_t)4;
    sim.simulator_stats.br_num += 1;
    BTB[pcIdx].target = targetPc;
    if(BTB[pcIdx].tag == MAX_PC){
        BTB[pcIdx].tag = pcTag;
        BTB[pcIdx].local_history_reg = NO_HISTORY_YET;
        if(!sim.global_pred_table){
            BTB[pcIdx].local_pred_machine = malloc((int)pow(2,sim.histSize)*sizeof(Bstate));
            if(BTB[pcIdx].local_pred_machine){
                for(int  i = 0 ; i < (int)pow(2,sim.histSize) ; i++){
                    BTB[pcIdx].local_pred_machine[i] = sim.default_state;
                }
            } else {
                free_everything();
                return;
            }
        }
    }
    if(BTB[pcIdx].tag != pcTag) {
        BTB[pcIdx].tag = pcTag;
        BTB[pcIdx].local_history_reg = NO_HISTORY_YET;
        if (!sim.global_pred_table) {
            for (int i = 0; i < (int) pow(2, sim.histSize); i++) {
                BTB[pcIdx].local_pred_machine[i] = sim.default_state;
            }
        }
    }
    // update the suitable history register
    uint32_t pcHistIdx = sim.global_his ? sim.global_his_reg & calcHistMask(sim.histSize) :
                         BTB[pcIdx].local_history_reg & calcHistMask(sim.histSize);
    if(sim.global_pred_table){
        if(sim.share_type == LSB){
            uint32_t pcLSB = pc & (calcHistMask(sim.histSize)*(uint32_t)4);
            pcLSB /= (uint32_t)4;
            pcHistIdx ^= pcLSB;
        }
        if(sim.share_type == MID) {
            uint32_t pcMID = pc & (calcHistMask(sim.histSize)*(uint32_t) pow(2, 16));
            //the next line is suspecious, it might be >> 4
            pcMID /= (uint32_t)(pow(2,16));
            pcHistIdx ^= pcMID;
        }
    }
    if(sim.global_his){
        sim.global_his_reg *= (uint8_t)2;
        sim.global_his_reg += taken;
    } else {
        BTB[pcIdx].local_history_reg *= (uint8_t)2;
        BTB[pcIdx].local_history_reg += taken;
    }
    if(taken){
        if(sim.global_pred_table){
            sim.global_pred_machine[pcHistIdx] = stateIncrement(sim.global_pred_machine[pcHistIdx],INCREMENT);
        } else{
            BTB[pcIdx].local_pred_machine[pcHistIdx] = stateIncrement(BTB[pcIdx].local_pred_machine[pcHistIdx],INCREMENT);
        }
        if(targetPc != pred_dst){
            sim.simulator_stats.flush_num += 1;
        }
    }
    if(!taken){
        if(sim.global_pred_table){
            sim.global_pred_machine[pcHistIdx] = stateIncrement(sim.global_pred_machine[pcHistIdx],DECREMENT);
        } else{
            BTB[pcIdx].local_pred_machine[pcHistIdx] = stateIncrement(BTB[pcIdx].local_pred_machine[pcHistIdx],DECREMENT);
        }
        if(pred_dst != pc + (uint32_t)4){
            sim.simulator_stats.flush_num += 1;
        }
    }
}

void BP_GetStats(SIM_stats *curStats){
    *curStats = sim.simulator_stats;
    free_everything();
}

