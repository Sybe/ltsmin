/*
 * pins2pins-parallel.c
 *
 *  Created on: 2 dec. 2014
 *      Author: sybe
 */
#include <hre/config.h>

#include <stdlib.h>

#include <hre/user.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <pins-lib/pins.h>


static model_t *models;     //Array of models to be composed
static int model_count;     //Number of models to be composed
static int bool_type;       //Boolean type

static int iomapa = 0;
static int input_enabled = 0;

static int *input_enabled_groups;

static int TAU;
static int INTERN;
static int OUTPUT;
static int INPUT;
static int RATE;

#define MAX_LABEL_LENGTH 100

typedef matrix_t* (*matrixCall)(model_t model);

typedef struct{
    void *ctx;       //Original Context
    int  *state;     //A state
    int model_nr;    //The number of the model, equal to the position in the models array
    TransitionCB cb; //The original callback function
    int group;       //The transition group
    int sync;        //True if it is a synchronizing transition
    int *groups;     //The original transition groups
    model_t model;   //The composed model
    char* label;     //The label of the action
    int result;      //If synchronization succeeds this is set to 1, else to 0
    int *state_vars; //The number of state vars per model
} parrallel_ctx ;

typedef struct{
    int label;
} label_ctx;

typedef struct{
    int **map;
    int *length;
    int maxLength;
} mapping_t;         //Mapping for the action chunks

static int **sync_groups;
static int sync_groups_length;
static size_t sync_groups_maxLength;

static mapping_t* map;

/**
 * Strips the '!' or '?' from the label and any variables after that character
 * Needed to check if a input and output action can synchronize
 * Only useful when the variable is not set to a value yet
 */
void
strip_io_label_complete(char* label){
    for(int i = 0; i < MAX_LABEL_LENGTH && label[i] != '\0'; i++){
        if(label[i] == '?' || label[i] == '!'){
            while(label[i] != '\0'){
                label[i] = '\0';
                i++;
            }
        }
    }
}
/**
 * Strips the '!' or '?' from the label
 * Needed to check if a input and output action can synchronize
 */
void
strip_io_label(char* label){
    for(int i = 0; i < MAX_LABEL_LENGTH && label[i] != '\0'; i++){
        if(label[i] == '?' || label[i] == '!'){
            i++;
            while(label[i - 1] != '\0'){
                label[i - 1] = label[i];
                i++;
            }
        }
    }
}

/**
 * Strips any variables in a label
 */
void
strip_label(char* label){
    for(int i = 1; i < MAX_LABEL_LENGTH && label[i] != '\0'; i++){
        if(label[i] == '('){
            while(label[i] != '\0'){
                label[i] = '\0';
                i++;
            }
        }
    }
}

/**
 * Checks if string is already in stringArray, an array of strings
 */
static int
string_in_array(char* string, char** stringArray, int arrayLength){
    for(int i = 0; i < arrayLength ; i++){
        if(strcmp(string,stringArray[i]) == 0){
            return 1;
        }
    }
    return 0;
}

/**
 * Sets a mapping for the action chunks
 */
static void
map_chunk(int model, int from, int to){
    if(map->length[model] == map->maxLength){
        for(int i = 0; i < model_count; i++){
            int *t = realloc(map->map[i], (size_t)(2*map->maxLength*sizeof(int)));
            map->map[i] = t;
        }
        map->maxLength = map->maxLength * 2;
    }
    map->map[model][from] = to;
    map->length[model] += 1;
}

/**
 * Returns the mapping for the action chunks
 */
static int
get_chunk(int model, int from){
    return map->map[model][from];
}


// Mapa specific
/**
 * Sets all state label chunks after the state space generation has been done.
 */
void
set_chunks(model_t model){
    int state_vars_counted = 0;
    int bools_counted = 0;
    //Dit specifiek voor states labels
    for(int i = 0; i < model_count; i++){
        int j;
        char* labels[lts_type_get_state_length(GBgetLTStype(models[i]))];
        int nrOfLabels = 0;
        for(j = 0; j < lts_type_get_state_length(GBgetLTStype(models[i])) && strcmp(lts_type_get_state_type(GBgetLTStype(models[i]), j), "Bool") != 0; j++){
            if(strcmp(lts_type_get_state_type(GBgetLTStype(models[i]), j), "Bool") != 0 && !string_in_array(lts_type_get_state_type(GBgetLTStype(models[i]), j), labels, nrOfLabels)){
                labels[nrOfLabels] = lts_type_get_state_type(GBgetLTStype(models[i]), j);
                nrOfLabels++;
                for(int k = 0; k < GBchunkCount(models[i], j + 1 - bools_counted); k++){
                    chunk c = GBchunkGet(models[i], j + 1 - bools_counted, k);
                    GBchunkPutAt(model, j + state_vars_counted + 1 - bools_counted, c, k);
                }
            } else {
                bools_counted++;
            }
        }
        state_vars_counted += j - bools_counted;
        bools_counted = 0;
    }
}

/*
 * Sets a group that should synchronize according to the numbers in groups
 * A value is -1 if a group does not syncronize for this action
 */
void
add_sync_group(int *groups){
    for(int i = 0; i < sync_groups_length; i++){
        int equal = 1;
        for(int j = 0; j < model_count; j++){
            equal &= (sync_groups[i][j] == groups[j]);
        }
        if(equal){
            return;
        }
    }
    if(sync_groups_length == (int)sync_groups_maxLength){
        int *first_group = malloc(model_count * sizeof(int));
        for(int i = 0; i < model_count; i++){
            first_group[i] = sync_groups[0][i];
        }
        if(input_enabled){
            input_enabled_groups = realloc(input_enabled_groups, ((size_t)(sync_groups_maxLength * 2 * sizeof(int*))));
        }
        int** tmp = realloc(*sync_groups, (size_t)(sync_groups_maxLength * 2 * sizeof(int*)));
        sync_groups_maxLength *= 2;
        for(int i = 0; i < model_count; i++){
            tmp[0] = first_group;
        }
        for(int i = 1; i < sync_groups_length; i++){
            int* newGroup = malloc(model_count * sizeof(int));
            tmp[i] = newGroup;
            for(int j = 0; j < model_count; j++){
                tmp[i][j] = sync_groups[i][j];
            }
        }
        sync_groups = tmp;
    }
    int id[model_count];
    if(input_enabled){
        for(int i = 0; i < model_count; i++){
            id[i] = GBgetMatrixID(models[i],LTSMIN_EDGE_TYPE_ACTION_CLASS);
        }
    }
    int *newGroups = malloc(model_count * sizeof(int));
    int total_groups = 0;
    int output_group = -1;
    for (int i = 0; i < model_count; i++){
        newGroups[i] = groups[i];
        if(groups[i] != -1){
            total_groups++;
            if(input_enabled){
                if(dm_is_set(GBgetMatrix(models[i], id[i]), OUTPUT, groups[i])){
                    output_group = i;
                }
            }
        }
    }
    sync_groups[sync_groups_length] = newGroups;
    if(input_enabled){
        input_enabled_groups[sync_groups_length] = 0;
    }
    sync_groups_length++;
}

/**
 * Returns the last added synchronization group.
 * Returns -1 if no group has been added yet
 */
int
get_last_sync_group(int *dest){
    int result;
    if (sync_groups_length == 0){
        result = -1;
    } else {
        int group = sync_groups_length - 1;
        if(input_enabled){
            for (; group >=0; group--){
                if(input_enabled_groups[group] == 0){
                    break;
                }
            }
        }
        for(int i = 0; i < model_count; i++)
        dest[i] = sync_groups[group][i];
        result = 0;
    }
    return result;
}

/**
 * Returns the synchronization group on position group
 */
int
get_sync_group(int group, int *dest){
    int result;
    if(group >= sync_groups_length){
        result = -1;
    } else {
        memcpy(dest, sync_groups[group], model_count*sizeof(int));
        result = 0;
    }
    return result;
}

/**
 * Inits an array with value -1 at all positions
 */
void
init_array(int *array, int length){
    for(int i = 0; i < length; i++){
        array[i] = -1;
    }
}

/**
 * Compares two arrays of int's. Returns 1 if equal, 0 if not equal
 */
int
compare_int_array(int *array1, int *array2, int length){
    int equal = 1;
    for(int i = 0; i < length && equal; i++){
        equal = array1[i] == array2[i];
    }
    return equal;
}

/**
 * Combines matrices according to the sync groups created earlier
 */
void
combineMatrices(matrixCall mc, model_t *models, matrix_t *dst){
    int columns[model_count];
    int columns_total = 0;
    for(int i = 0; i < model_count; i++){
        columns_total += dm_ncols(mc(models[i]));
    }
    dm_create(dst, sync_groups_length, columns_total);
    for(int i = 0; i < sync_groups_length; i++){
        if(input_enabled && input_enabled_groups[i]){
            for(int j = 0; j < dm_ncols(dst); j++){
                if(dm_is_set(dst, i - 1, j)){
                    dm_set(dst, i , j);
                }
            }
        } else {
            int cols_created = 0;
            for(int j = 0; j < model_count; j++){
                for(int k = 0; k < dm_ncols(mc(models[j])); k++){
                    if(sync_groups[i][j] != -1 && dm_is_set(mc(models[j]), sync_groups[i][j], k)){
                        dm_set(dst, i, k + cols_created);
                    }
                }
                cols_created += dm_ncols(mc(models[j]));
            }
        }
    }
}

/**
 * Combines the State Label matrices of multiple models
 */
void combineSLMatrices(model_t *models, matrix_t *dst){
    int columns[model_count];
    int rows = dm_nrows(GBgetStateLabelInfo(models[0]));
    int columns_total = 0;
    for(int i = 0; i < model_count; i++){
        columns[i]      = dm_ncols(GBgetStateLabelInfo(models[i]));
        columns_total   += columns[i];
    }
    int columns_created = 0;
    dm_create(dst, rows, columns_total);
    for(int i = 0; i < model_count; i++){
        for(int j = 0; j < columns[i]; j++){
            for(int k = 0; k < rows; k++){
                if(dm_is_set(GBgetStateLabelInfo(models[i]), k, j)){
                    dm_set(dst, k, j + columns_created);;
                }
            }
        }
        columns_created += columns[i];
    }
}
void
create_io_groups_recursive(int groups_count, int model_count, char labels[model_count][groups_count][MAX_LABEL_LENGTH], int types[model_count][groups_count], int model, int group, char *label, int new_groups[model_count]){
    if(strcmp(label, "") == 0){
        //If the label is "" a new group can be formed
        for(int i = group; i < dm_nrows(GBgetDMInfo(models[model])); i++){
            if(types[model][i] == TAU || types[model][i] == RATE || types[model][i] == INTERN){
                //If a new group is a tau, internal action or a rate, it can be created immediately
                int new_group[model_count];
                init_array(new_group, model_count);
                new_group[model] = i;
                add_sync_group(new_group);
            } else {
                //Else it is an input/output action
                char group_label[MAX_LABEL_LENGTH];
                strcpy(group_label, labels[model][i]);
                strip_io_label(group_label);
                int new_label = 1;
                for(int j = 0; j < model && new_label; j++){
                    //Check if this label is not present at models already evaluated
                    for(int k = 0; k < dm_nrows(GBgetDMInfo(models[j])) && new_label; k++){
                        char compare_label[MAX_LABEL_LENGTH];
                        strcpy(compare_label, labels[j][k]);
                        strip_io_label(compare_label);
                        if(strcmp(group_label, compare_label) == 0){
                            new_label = 0;
                        }
                    }
                }
                //If not a new_label, it has already been created at an earlier point
                if(new_label){
                    int new_group[model_count];
                    init_array(new_group, model_count);
                    new_group[model] = i;
                    if(model < model_count - 1){
                        //Check recursively if the action can synchronize
                        create_io_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, group_label, new_group);
                        int last_added_groups[model_count];
                        int last_returned_groups[model_count];
                        for(int j = 0; j < model_count; j++){
                            last_returned_groups[j] = new_group[j];
                        }
                        if(get_last_sync_group(last_added_groups) != -1){
                            if(last_added_groups[model] == i){
                                while(last_added_groups[model + 1] != -1 && compare_int_array(last_added_groups, last_returned_groups, model_count)){
                                    if(new_groups == NULL){
                                        new_groups = new_group;
                                    }
                                    new_groups[model] = i;
                                    for(int j = model + 1; j < model_count; j++){
                                        new_groups[j] = -1;
                                    }
                                    for(int j = 0; j < model_count; j++){
                                        last_returned_groups[j] = new_groups[j];
                                    }
                                    get_last_sync_group(last_added_groups);
                                }
                            }
                        }
                    } else {
                        add_sync_group(new_group);
                    }
                }
            }
        }
        if(model < model_count - 1){
            //If this is not the last model, run the recursion for the next model
            create_io_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, "", NULL);
        }
    } else {
        //If the function is called with a label, a synchronizing action should be searched
        int synchronizing_group_found = 0;
        for(int i = group; i < dm_nrows(GBgetDMInfo(models[model])); i++){
            //Checking for all groups in this model
            if (types[model][i] == INPUT || types[model][i] == OUTPUT){
                char compare_label[MAX_LABEL_LENGTH];
                strcpy(compare_label, labels[model][i]);
                strip_io_label(compare_label);
                if(strcmp(compare_label, label) == 0){
                    //A synchronizing action has been found
                    synchronizing_group_found = 1;
                    new_groups[model] = i;
                    if(model < model_count - 1){
                        //If this is not the last model, the recursion goes deeper to look for a synchronizig action in the next model
                        create_io_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, label, new_groups);
                        int last_added_groups[model_count];
                        int last_returned_groups[model_count];
                        for(int j = 0; j < model_count; j++){
                            last_returned_groups[j] = new_groups[j];
                        }
                        if(get_last_sync_group(last_added_groups) != -1){
                            int deep_group_found = 1;
                            while(last_added_groups[model] != -1 && !compare_int_array(last_added_groups, last_returned_groups, model_count) && deep_group_found){
                                //While groups get added, we start the recursion again to find more synchronizing groups
                                deep_group_found = 0;
                                for(int j = model; j < model_count; j++){
                                    new_groups[j] = -1;
                                }
                                create_io_groups_recursive(groups_count, model_count, labels, types, model + 1, last_added_groups[model + 1], label, new_groups);
                                for(int j = 0; j < model_count; j++){
                                    last_returned_groups[j] = new_groups[j];
                                }
                                get_last_sync_group(last_added_groups);
                                for(int j = model + 1; j < model_count; j++){
                                    deep_group_found |= last_returned_groups[j] != -1;
                                }
                            }
                        }
                    } else {
                        //If this is the last model, the group can be added
                        add_sync_group(new_groups);
                    }
                }
            }
        }
        //(if not just a group created and not a group with this label already created,
        int last_added_groups[model_count];
        if(get_last_sync_group(last_added_groups) != -1){
            if(!synchronizing_group_found){
                if(model < model_count - 1){
                    create_io_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, label, new_groups);
                } else {
                    add_sync_group(new_groups);
                }
            }
        } else {
            if(model < model_count - 1){
                create_io_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, label, new_groups);
            } else {
                add_sync_group(new_groups);
            }
        }
    }

}

void
create_groups_recursive(int groups_count, int model_count, char labels[model_count][groups_count][MAX_LABEL_LENGTH], int types[model_count][groups_count], int model, int group, char *label, int new_groups[model_count]){
    if(strcmp(label, "") == 0){
        //If the label is "" a new group can be formed
        for(int i = group; i < dm_nrows(GBgetDMInfo(models[model])); i++){
            if(types[model][i] == TAU || types[model][i] == RATE){
                //If a new group is a tau or a rate, it can be created immediately
                int new_group[model_count];
                init_array(new_group, model_count);
                new_group[model] = i;
                add_sync_group(new_group);
            } else {
                //Else it is a action with a label
                char group_label[MAX_LABEL_LENGTH];
                strcpy(group_label, labels[model][i]);
                strip_label(group_label);
                int new_label = 1;
                for(int j = 0; j < model && new_label; j++){
                    //Check if this label is not present at models already evaluated
                    for(int k = 0; k < dm_nrows(GBgetDMInfo(models[j])) && new_label; k++){
                        char compare_label[MAX_LABEL_LENGTH];
                        strcpy(compare_label, labels[j][k]);
                        strip_label(compare_label);
                        if(strcmp(group_label, compare_label) == 0){
                            new_label = 0;
                        }
                    }
                }
                //If not a new_label, it has already been created at an earlier point
                if(new_label){
                    int new_group[model_count];
                    init_array(new_group, model_count);
                    new_group[model] = i;
                    if(model < model_count - 1){
                        //Check recursively if the action can synchronize
                        create_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, group_label, new_group);
                        int last_added_groups[model_count];
                        int last_returned_groups[model_count];
                        for(int j = 0; j < model_count; j++){
                            last_returned_groups[j] = new_group[j];
                        }
                        if(get_last_sync_group(last_added_groups) != -1){
                            if(last_added_groups[model] == i){
                                while(last_added_groups[model + 1] != -1 && compare_int_array(last_added_groups, last_returned_groups, model_count)){
                                    if(new_groups == NULL){
                                        new_groups = new_group;
                                    }
                                    new_groups[model] = i;
                                    for(int j = model + 1; j < model_count; j++){
                                        new_groups[j] = -1;
                                    }
                                    for(int j = 0; j < model_count; j++){
                                        last_returned_groups[j] = new_groups[j];
                                    }
                                    get_last_sync_group(last_added_groups);
                                }
                            }
                        }
                    } else {
                        add_sync_group(new_group);
                    }
                }
            }
        }
        if(model < model_count - 1){
            //If this is not the last model, run the recursion for the next model
            create_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, "", NULL);
        }
    } else {
        //If the function is called with a label, a synchronizing action should be searched
        int synchronizing_group_found = 0;
        for(int i = group; i < dm_nrows(GBgetDMInfo(models[model])); i++){
            //Checking for all groups in this model
            if (types[model][i] == INTERN){
                char compare_label[MAX_LABEL_LENGTH];
                strcpy(compare_label, labels[model][i]);
                strip_label(compare_label);
                if(strcmp(compare_label, label) == 0){
                    //A synchronizing action has been found
                    synchronizing_group_found = 1;
                    new_groups[model] = i;
                    if(model < model_count - 1){
                        //If this is not the last model, the recursion goes deeper to look for a synchronizig action in the next model
                        create_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, label, new_groups);
                        int last_added_groups[model_count];
                        int last_returned_groups[model_count];
                        for(int j = 0; j < model_count; j++){
                            last_returned_groups[j] = new_groups[j];
                        }
                        if(get_last_sync_group(last_added_groups) != -1){
                            int deep_group_found = 1;
                            while(last_added_groups[model] != -1 && !compare_int_array(last_added_groups, last_returned_groups, model_count) && deep_group_found){
                                //While groups get added, we start the recursion again to find more synchronizing groups
                                deep_group_found = 0;
                                for(int j = model; j < model_count; j++){
                                    new_groups[j] = -1;
                                }
                                create_groups_recursive(groups_count, model_count, labels, types, model + 1, last_added_groups[model + 1], label, new_groups);
                                for(int j = 0; j < model_count; j++){
                                    last_returned_groups[j] = new_groups[j];
                                }
                                get_last_sync_group(last_added_groups);
                                for(int j = model + 1; j < model_count; j++){
                                    deep_group_found |= last_returned_groups[j] != -1;
                                }
                            }
                        }
                    } else {
                        //If this is the last model, the group can be added
                        add_sync_group(new_groups);
                    }
                }
            }
        }
        //(if not just a group created and not a group with this label already created,
        int last_added_groups[model_count];
        if(get_last_sync_group(last_added_groups) != -1){
            if(!synchronizing_group_found){
                if(model < model_count - 1){
                    create_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, label, new_groups);
                } else {
                    add_sync_group(new_groups);
                }
            }
        } else {
            if(model < model_count - 1){
                create_groups_recursive(groups_count, model_count, labels, types, model + 1, 0, label, new_groups);
            } else {
                add_sync_group(new_groups);
            }
        }
    }

}

/*
 * Reads the input txt files in mlppe format and based on those
 * creates an array which decides what groups to evaluate
 */
// MAPA specific
void
create_correct_groups(char **files, int file_count){
    int max_groups = 0;
    for (int i = 0; i < file_count; i++){
        if(dm_nrows(GBgetDMInfo(models[i])) > max_groups){
            max_groups = dm_nrows(GBgetDMInfo(models[i]));
        }
    }
    char labels[file_count][max_groups][MAX_LABEL_LENGTH];
    int types[file_count][max_groups];

    for(int i = 0; i < file_count; i++){
        Warning(info, "opening mlppe file %s", files[i]);
        FILE *f = fopen(files[i], "r");
        char c;
        int group = 0;
        while ((c = getc(f)) != EOF){
            if(c == '='){
                char c1 = getc(f);
                if(c1 == '>'){
                    getc(f);//Space
                    char label[MAX_LABEL_LENGTH];
                    HREassert(fscanf(f, "%s", label) == 1);
                    strcpy(labels[i][group], label);
                    if (label != NULL){
                        switch(label[0]){
                        case '(' :
                            types[i][group] = RATE;
                            break;
                        default :
                            if (strcmp(label, "tau") == 0) {
                                types[i][group] = TAU;
                            } else {
                                if(strchr(label,  '?') != NULL){
                                    types[i][group] = INPUT;
                                } else {
                                    if(strchr(label,  '!') != NULL){
                                        types[i][group] = OUTPUT;
                                    } else {
                                        types[i][group] = INTERN;
                                    }
                                }
                            }
                            break;
                        }
                    }
                    group++;
                }
            }
        }
    }
    Warning(info, "mlppe files closed");
    int groups[model_count];
    if(iomapa){
        create_io_groups_recursive(max_groups, file_count, labels, types, 0, 0, "", groups);
    } else {
        create_groups_recursive(max_groups, file_count, labels, types, 0, 0, "", groups);
    }
}


/**
 * Basic callback function that also returns to the original callback function.
 * Used for non synchronizing groups and final groups to call
 */
static void parallel_cb (void*context,transition_info_t*transition_info,int*dst,int*cpy){
    parrallel_ctx*ctx = (parrallel_ctx*) context;
    int columns[model_count];
    int columns_total = 0;
    //Columns represent columns in the matrices, or the number of state labels
    for(int i = 0; i < model_count; i++){
        columns[i] = lts_type_get_state_length(GBgetLTStype(models[i]));
        columns_total += columns[i];
    }
    int dest[columns_total];//The state to return
    int cols_counted = 0;
    for(int i = 0; i < model_count; i++){
        if(ctx->model_nr == i){//If the callback is for this model, the dest can be copied from dst
            for(int j = 0; j < columns[i]; j++){
                dest[j + cols_counted]=dst[j];
            }
        } else {//Else the dest can be copied from ctx->state which has earlier been filled by synchronizing actions
            for(int j = 0; j < columns[i]; j++){
                dest[j + cols_counted] = ctx->state[j + cols_counted];
            }
        }
        cols_counted += columns[i];
    }
    transition_info_t ti = GB_TI(transition_info->labels, ctx->group);
    ti.labels[3] = ctx->group;//Make a new transition info, and add the number of the combined group
    int actions = 0;
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(ctx->model)); i++){
        if(strcmp(lts_type_get_type(GBgetLTStype(ctx->model), i),"action") == 0){
            actions = i;//The type number of "action" in the combined model
        }
    }
    int old_actions = 0;
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(models[ctx->model_nr])); i++){
        if(strcmp(lts_type_get_type(GBgetLTStype(models[ctx->model_nr]), i),"action") == 0){
            old_actions = i;//The type number of "action" in the original model
        }
    }
    chunk c = GBchunkGet(models[ctx->model_nr], old_actions, ti.labels[2]);//The chunk of this action in the original model
    if(ctx->sync){
        char* label = malloc(MAX_LABEL_LENGTH * sizeof(char));
        strcpy(label, c.data);
        if(iomapa){
            strip_io_label(label);
        }
        if(strcmp(label, ctx->label) == 0){//Check if synchronization is indeed correct
            int pos = GBchunkPut(ctx->model, actions, c);//Putting the chunk of the actionlabel in the combined model
            map_chunk(ctx->model_nr, ti.labels[2], pos);//Make a mapping from the chunk number in the original model to the number in the combined model
            //Mapa specific
            ti.labels[2] = get_chunk(ctx->model_nr, ti.labels[2]);//Put the chunk number in the transition info
            ctx->cb(ctx->ctx, &ti, dest, cpy);//Call the original callback
            ctx->result = 1;
        } else {
            //If incorrect synchronization, return 0 and do nothing
            ctx->result = 0;
        }
    } else {
        int pos = GBchunkPut(ctx->model, actions, c);
        map_chunk(ctx->model_nr, ti.labels[2], pos);
        //Mapa specific
        ti.labels[2] = get_chunk(ctx->model_nr, ti.labels[2]);
        ctx->cb(ctx->ctx, &ti, dest, cpy);
        ctx->result = 1;
    }
}

/**
 * Callback function for synchronizing actions
 * Do not call this function for the last model in a synchronization
 */
static void parallel_sync_cb(void*context,transition_info_t*transition_info,int*dst,int*cpy){
    parrallel_ctx*ctx = (parrallel_ctx*)context;
    int actions = 0;
    for (int i = 0; i < lts_type_get_type_count(GBgetLTStype(models[ctx->model_nr])); i++){
        if(strcmp(lts_type_get_type(GBgetLTStype(models[ctx->model_nr]), i),"action") == 0){
            actions = i;//The type number of "action" in the original model
        }
    }
    chunk c = GBchunkGet(models[ctx->model_nr], actions, transition_info->labels[2]);//Getting the chunk to extract the action label
    char* label=malloc(MAX_LABEL_LENGTH * sizeof(char));
    strcpy(label, c.data);
    if(iomapa){
        strip_io_label(label);
    }
    static char ctxLabel[MAX_LABEL_LENGTH];
    if (ctx->label == NULL){
        ctx->label = ctxLabel;
        strcpy(ctx->label, label);
        ctx->result = 1;
    } else {
        if (strcmp(ctx->label, label)!=0){//If incorrect synchronization, return a result of 0, indication that this action should not be executed
            ctx->result = 0;
        }
    }
    free(label);
    if(ctx->result == 1){
        int columns = lts_type_get_state_length(GBgetLTStype(models[ctx->model_nr]));
        int start_column = 0;
        for(int i = 0; i < ctx->model_nr; i++){
            start_column += lts_type_get_state_length(GBgetLTStype(models[i]));
        }
        for(int i = 0; i < columns; i++){
            ctx->state[i + start_column] = dst[i];//Filling the part of the state that changes by this transition
        }
    }
    (void)cpy;
}

static void label_cb(void*context,transition_info_t*transition_info,int*dst,int*cpy){
    label_ctx*ctx = (label_ctx*)context;
    ctx->label = transition_info->labels[2];
    (void)transition_info;
    (void)dst;
    (void)cpy;
}

/*
 * Next state function
 */
// Mapa specific
int
getTransitionsLong (model_t m, int group, int *src, TransitionCB cb, void *ctx)
{
    fflush(stdout);
    parrallel_ctx *context = malloc(sizeof(parrallel_ctx));
    label_ctx* labelContext = malloc(sizeof(label_ctx));
    labelContext->label = -1;
    context->ctx = ctx;
    int stateLength = lts_type_get_state_length(GBgetLTStype(m));
    context->state = malloc(stateLength * sizeof(int));
    for(int i = 0; i < stateLength; i++){
        context->state[i] = src[i]; //Need to copy this element wise
    }
    context->cb = cb;
    context->group = group;
    context->sync = 0;
    context->model = m;
    context->result = 1;
    context->label = NULL;
    int result = 1;
    int state_vars[model_count];
    int total_models = 0;
    int active_models[model_count];
    for(int i = 0; i < model_count; i++){
        state_vars[i] = lts_type_get_state_length (GBgetLTStype(models[i]));
        if(sync_groups[group][i] != -1){
            active_models[total_models] = i;//Creating an array of all models that take part in this transition
            total_models++;//The number of model that take part in this transition
        }
    }
    context->state_vars = state_vars;
    if (total_models == 1){//It is a non-synchronizing action
        context->model_nr = active_models[0];
        int state_vars_counted = 0;
        for(int i = 0; i < active_models[0]; i++){
            state_vars_counted += state_vars[i];
        }
        int source[state_vars[active_models[0]]];
        for(int j = 0; j < state_vars[active_models[0]]; j++){
            source[j] = src[j + state_vars_counted];
        }
        result = GBgetTransitionsLong(models[active_models[0]], sync_groups[group][active_models[0]], source, parallel_cb, context);
    } else {
        context->sync = 1;
        if(iomapa){
            int id = GBgetMatrixID(m,LTSMIN_EDGE_TYPE_ACTION_CLASS);
            if(dm_is_set(GBgetMatrix(m, id), OUTPUT, group) || !dm_is_set(GBgetMatrix(m, id), INPUT, group)){
                for(int i = 0; i < total_models - 1; i++){
                    int local_id = GBgetMatrixID(models[active_models[i]],LTSMIN_EDGE_TYPE_ACTION_CLASS);
                    if(dm_is_set(GBgetMatrix(models[active_models[i]], local_id), OUTPUT, sync_groups[group][active_models[i]])){
                        for(int j = i; j < total_models - 1; j++){
                            int output_model = active_models[j];
                            active_models[j] = active_models[j + 1];
                            active_models[j + 1] = output_model;
                        }
                    }
                }
            }
        }
        int failed_model = -1;
        for(int i = 0; i < total_models - 1; i++){//Loop for all synchronizing actions, except the last
            //Loop is terminated if one of the callback functions detects incorrect synchronization, or if one of the synchronizing actions cannot be executed from current state
            int state_vars_counted = 0;
            for(int j = 0; j < active_models[i]; j++){
                state_vars_counted += state_vars[j];
            }
            int source[state_vars[active_models[i]]];//Source for this transition
            for(int j = 0; j < state_vars[active_models[i]]; j++){
                source[j] = src[j + state_vars_counted];
            }
            context->model_nr = active_models[i];//The number of the original model

            result = GBgetTransitionsLong(models[active_models[i]], sync_groups[group][active_models[i]], source, parallel_sync_cb, context);
            if(result == 0 || context->result == 0){
                failed_model = active_models[i];
                if(input_enabled){
                    state_vars_counted = 0;
                    for(int j = 0; j < active_models[total_models - 1]; j++){
                        state_vars_counted += state_vars[j];
                    }
                    source[state_vars[active_models[i]]];//Source for this transition
                    for(int j = 0; j < state_vars[total_models - 1]; j++){
                        source[j] = src[j + state_vars_counted];
                    }
                    GBgetTransitionsLong(models[active_models[total_models - 1]], sync_groups[group][active_models[total_models - 1]], source, label_cb, labelContext);
                    if(labelContext->label == -1){
                        break;
                    }
                    int actions = -1;
                    for (int j = 0; j < lts_type_get_type_count(GBgetLTStype(models[active_models[total_models - 1]])); j++){
                        if(strcmp(lts_type_get_type(GBgetLTStype(models[active_models[total_models - 1]]), j),"action") == 0){
                            actions = j;
                            break;
                        }
                    }
                    char output_label[MAX_LABEL_LENGTH];
                    chunk output_chunk = GBchunkGet(models[active_models[total_models - 1]], actions, labelContext->label);
                    strcpy(output_label, output_chunk.data);
                    strip_io_label(output_label);

                    for (int j = 0; j < lts_type_get_type_count(GBgetLTStype(models[failed_model])); j++){
                        if(strcmp(lts_type_get_type(GBgetLTStype(models[failed_model]), j),"action") == 0){
                            actions = j;//The type number of "action" in the original model
                        }
                    }
                    int state_vars_counted = 0;
                    for(int j = 0; j < failed_model; j++){
                        state_vars_counted += state_vars[j];
                    }
                    int source[state_vars[failed_model]];
                    for(int j = 0; j < state_vars[failed_model]; j++){
                        source[j] = src[j + state_vars_counted];
                    }
                    int found = 0;
                    for(int j = 0; j < dm_nrows(GBgetDMInfo(models[failed_model])); j++){
                        int local_result = GBgetTransitionsLong(models[failed_model], j, source, label_cb, labelContext);
                        if(local_result > 0){
                            chunk c = GBchunkGet(models[failed_model], actions, labelContext->label);
                            char local_label[MAX_LABEL_LENGTH];
                            strcpy(local_label, c.data);
                            strip_io_label(local_label);
                            if(strcmp(local_label, output_label) == 0){
                                found = 1;
                                break;
                            }
                        }
                    }
                    if(found){
                        break;
                    } else {
                        for(int j = 0; j < group; j++){
                            if(sync_groups[j][failed_model] == sync_groups[group][failed_model]){
                                found = 1;
                                break;
                            }
                        }
                        if(found){
                            break;
                        } else {
                        result = 1;
                        context->result = 1;
                        }
                    }
                }
                break;
            }
        }
        if(result > 0 && context->result > 0){//For the last synchronizing action, and if synchronization is still correct
            if(context->label == NULL){
                context->sync = 0;
            }
            int state_vars_counted = 0;
            for(int j = 0; j < active_models[total_models - 1]; j++){
                state_vars_counted += state_vars[j];
            }
            int source[state_vars[active_models[total_models - 1]]];
            for(int j = 0; j < state_vars[active_models[total_models - 1]]; j++){
                source[j] = src[j + state_vars_counted];
            }
            context->model_nr = active_models[total_models - 1];

            result = GBgetTransitionsLong(models[active_models[total_models - 1]], sync_groups[group][active_models[total_models - 1]], source, parallel_cb, context);
        }
    }
    context->label = NULL;
    if(context->result == 0){//If callback detected incorrect synchronization, result is set to 0
        result = 0;
    }
    free(context->state);
    free(context);
    return result;
}

/**
 * GetTransitionsAll, works only for full max progress
 */
int
getTransitionsAll(model_t model,int*src,TransitionCB cb,void*context){
    int id = GBgetMatrixID(model,LTSMIN_EDGE_TYPE_ACTION_CLASS);
    matrix_t *class_matrix = GBgetMatrix(model,id);
    int res = 0;
    res=GBgetTransitionsMarked(model,class_matrix,TAU,src,cb,context);
    res+=GBgetTransitionsMarked(model,class_matrix,INTERN,src,cb,context);
    if(iomapa){
        res+=GBgetTransitionsMarked(model,class_matrix,OUTPUT,src,cb,context);
    }
    if (res==0){
        res+=GBgetTransitionsMarked(model,class_matrix,RATE,src,cb,context);
        if(iomapa){
            res+=GBgetTransitionsMarked(model,class_matrix,INPUT,src,cb,context);
        }
    }
    return res;
}

/**
 * Implementation for GBgetStateLabelLong
 */
int
getStateLabelLong(model_t m, int label, int *state){
    (void)m;
    int result = -1;
    int labels[model_count];
    int state_vars[model_count];
    for(int i = 0; i < model_count; i++){
        labels[i] = lts_type_get_state_label_count(GBgetLTStype(models[i]));
        state_vars[i] = lts_type_get_state_length (GBgetLTStype(models[i]));
    }
    int labels_counted = 0;
    int state_vars_counted = 0;
    int model_found = 0;

    for(int i = 0; i < model_count && !model_found; i++){
        if(label < labels[i] + labels_counted && label >= labels_counted){
            model_found = 1;
            int local_state[state_vars[i]];
            for(int j = 0; j < state_vars[i]; j++){
                local_state[j] = state[j + state_vars_counted];
            }
            result = GBgetStateLabelLong(models[i], label - labels_counted, local_state);
        }
        labels_counted += labels[i];
        state_vars_counted += state_vars[i];
    }
    return result;
}


/*
 * Checks if all models have the matrix called by mc
 */
int
matrices_present(matrixCall mc, model_t *models){
    int result = 1;
    for(int i = 0; i < model_count; i++){
        result &= result && (mc(models[i]) != NULL);
    }
    return result;
}

void
put_mapa_lts_types(lts_type_t ltstype){
    int state_length = 0;
    int state_label_count = 0;
    int edge_label_count = 0;
    for (int i = 0; i < model_count; i++){
        state_length += lts_type_get_state_length (GBgetLTStype(models[i]));
        state_label_count += lts_type_get_state_label_count (GBgetLTStype(models[i]));
        edge_label_count += lts_type_get_edge_label_count (GBgetLTStype(models[i]));
    }
    lts_type_set_state_length(ltstype, state_length);
    lts_type_set_state_label_count(ltstype, state_label_count);
    lts_type_set_edge_label_count(ltstype, edge_label_count);

    int state_length_counted = 0;
    int edge_labels_counted = 0;
    int state_labels_counted = 0;
    for (int i = 0; i < model_count; i++){
        char model_nr_str[2];
        sprintf(model_nr_str, "%d", i);
        for (int j = 0; j < lts_type_get_state_length (GBgetLTStype(models[i])); j++){
            if(strcmp(lts_type_get_state_type(GBgetLTStype(models[i]), j), "Bool") != 0){
                char tmp[MAX_LABEL_LENGTH];
                strcpy(tmp, lts_type_get_state_name(GBgetLTStype(models[i]), j));
                strcat(strcat(tmp, "_"),model_nr_str);
                lts_type_set_state_name(ltstype, j + state_length_counted, tmp);
                strcpy(tmp, lts_type_get_state_type(GBgetLTStype(models[i]), j));
                strcat(strcat(tmp, "_"),model_nr_str);
                lts_type_set_state_type(ltstype, j + state_length_counted, tmp);
            } else {
                lts_type_set_state_name(ltstype, j + state_length_counted, lts_type_get_state_name(GBgetLTStype(models[i]), j));
                lts_type_set_state_type(ltstype, j + state_length_counted, lts_type_get_state_type(GBgetLTStype(models[i]), j));
            }
        }
        state_length_counted += lts_type_get_state_length (GBgetLTStype(models[i]));
        edge_labels_counted += lts_type_get_edge_label_count(GBgetLTStype(models[i]));
        state_labels_counted += lts_type_get_state_label_count(GBgetLTStype(models[i]));
    }
    lts_type_put_type(ltstype,"action",LTStypeChunk,NULL);
    lts_type_put_type(ltstype,"nat",LTStypeDirect,NULL);
    lts_type_put_type(ltstype,"pos",LTStypeDirect,NULL);

    lts_type_set_edge_label_count(ltstype,6);
    lts_type_set_edge_label_name(ltstype,0,"reward_numerator");
    lts_type_set_edge_label_type(ltstype,0,"nat");
    lts_type_set_edge_label_name(ltstype,1,"reward_denominator");
    lts_type_set_edge_label_type(ltstype,1,"pos");
    lts_type_set_edge_label_name(ltstype,2,LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    lts_type_set_edge_label_type(ltstype,2,LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    lts_type_set_edge_label_name(ltstype,3,"group");
    lts_type_set_edge_label_type(ltstype,3,"nat");
    lts_type_set_edge_label_name(ltstype,4,"numerator");
    lts_type_set_edge_label_type(ltstype,4,"nat");
    lts_type_set_edge_label_name(ltstype,5,"denominator");
    lts_type_set_edge_label_type(ltstype,5,"pos");

    lts_type_set_state_label_count(ltstype,3);
    lts_type_set_state_label_name(ltstype,0,"goal");
    lts_type_set_state_label_type(ltstype,0,"Bool");
    lts_type_set_state_label_name(ltstype,1,"state_reward_numerator");
    lts_type_set_state_label_type(ltstype,1,"nat");
    lts_type_set_state_label_name(ltstype,2,"state_reward_denominator");
    lts_type_set_state_label_type(ltstype,2,"pos");
}

//Mapa specific
void
GBparallelCompose (model_t composition, const char **files, int file_count, pins_loader_t loader)
{
    Warning(info, "GBparallelCompose");
    GBsetNextStateLong(composition, getTransitionsLong);
    GBsetNextStateAll(composition, getTransitionsAll);
    GBsetStateLabelLong(composition, getStateLabelLong);
    if(iomapa){
        TAU = 0;
        INTERN = 1;
        OUTPUT = 2;
        INPUT = 3;
        RATE = 4;
    } else {
        TAU = 0;
        INTERN = 1;
        RATE = 2;
        INPUT = -1;//Not used in standard mapa
        OUTPUT = -1;//Not used in standard mapa
    }
    Warning(info, "Initializing awesome parallel composition layer");

    if(file_count < 4){
        Abort("Trying to compose with only %d input files, at least 4 needed", file_count);
    }
    model_count = (int)(file_count / 2);

    models = malloc(model_count*sizeof(model_t));
    for(int i = 0; i < model_count; i++){
        models[i] = GBcreateBase();
        GBsetChunkMethods(models[i],HREgreyboxNewmap,HREglobal(),
                          HREgreyboxI2C,
                          HREgreyboxC2I,
                          HREgreyboxCAtI,
                          HREgreyboxCount);
        GBsetModelNr(models[i], i);
        Warning(info, "Starting loader for model %d", i);
        loader(models[i], files[i]);
    }

    map = malloc(sizeof(mapping_t));//Create a chunk mapping
    map->map = malloc(model_count * sizeof(int*));
    map->maxLength = model_count;
    map->length = malloc(model_count * sizeof(int));
    int total_groups = 0;

    map->maxLength = 10;//Chosen arbitrary to 10
    for(int i = 0; i < model_count; i++){
        map->map[i] = malloc((size_t)(map->maxLength*sizeof(int)));
        map->length[i] = 0;
        total_groups += dm_nrows(GBgetDMInfo(models[i]));
    }

    sync_groups_length = 0;
    sync_groups_maxLength = (size_t)total_groups;//Arbitrary chosen the sum of all individual transitions in all models
    sync_groups= malloc(sync_groups_maxLength * sizeof(int*));

    if(input_enabled){
        input_enabled_groups = malloc(sync_groups_maxLength * sizeof(int*));
    }

    //Mapa specific
    char** txtFiles = malloc(model_count * sizeof(char*));//The mlppe text files
    memcpy(txtFiles, &files[model_count], model_count * sizeof(char*));

    create_correct_groups(txtFiles, model_count);

    matrix_t *p_dm              = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_read         = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_may_write    = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_must_write   = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_expand       = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_project      = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_state_label  = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_commute      = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_NDS          = RTmalloc(sizeof(matrix_t));
    matrix_t *p_dm_NES          = RTmalloc(sizeof(matrix_t));

    if(matrices_present(GBgetDMInfo, models)){
        combineMatrices(GBgetDMInfo, models, p_dm);
        GBsetDMInfo(composition, p_dm);
    }
    if(matrices_present(GBgetDMInfoRead, models)){
        combineMatrices(GBgetDMInfoRead, models, p_dm_read);
        GBsetDMInfoRead(composition, p_dm_read);
    }
    if(matrices_present(GBgetDMInfoMayWrite, models)){
        combineMatrices(GBgetDMInfoMayWrite, models, p_dm_may_write);
        GBsetDMInfoMayWrite(composition, p_dm_may_write);
    }
    if(matrices_present(GBgetDMInfoMustWrite, models)){
        combineMatrices(GBgetDMInfoMustWrite, models, p_dm_must_write);
        GBsetDMInfoMustWrite(composition, p_dm_must_write);
    }
    if(matrices_present(GBgetExpandMatrix, models)){
        combineMatrices(GBgetExpandMatrix, models, p_dm_expand);
        GBsetExpandMatrix(composition, p_dm_expand);
    }
    if(matrices_present(GBgetProjectMatrix, models)){
        combineMatrices(GBgetProjectMatrix, models, p_dm_project);
        GBsetProjectMatrix(composition, p_dm_project);
    }
    if(matrices_present(GBgetDoNotAccordInfo, models)){
        combineMatrices(GBgetDoNotAccordInfo, models, p_dm_project);
        GBsetDoNotAccordInfo(composition, p_dm_project);
    }
    if(matrices_present(GBgetStateLabelInfo, models)){
        combineSLMatrices(models, p_dm_state_label);
        GBsetStateLabelInfo(composition, p_dm_state_label);
    }
    if(matrices_present(GBgetCommutesInfo, models)){
        combineMatrices(GBgetCommutesInfo, models, p_dm_commute);
        GBsetCommutesInfo(composition, p_dm_commute);
    }
    if(matrices_present(GBgetGuardNDSInfo, models)){
        combineMatrices(GBgetGuardNDSInfo, models, p_dm_NDS);
        GBsetGuardNDSInfo(composition, p_dm_NDS);
    }
    if(matrices_present(GBgetGuardNESInfo, models)){
        combineMatrices(GBgetGuardNESInfo, models, p_dm_NES);
        GBsetGuardNESInfo(composition, p_dm_NES);
    }

    //GBsetMatrix
    //Class matrix
    int id[model_count];
    int rows_class = 0;
    int class_matrix_needed = 1;
    for(int i = 0; i < model_count; i++){
        id[i] = GBgetMatrixID(models[i],LTSMIN_EDGE_TYPE_ACTION_CLASS);
        if (id[i] >= 0){
            rows_class = dm_nrows(GBgetMatrix(models[i], id[i]));
        } else {
            class_matrix_needed = 0;
        }
    }
    if(class_matrix_needed){
        static matrix_t p_dm_class;
        dm_create(&p_dm_class, rows_class, sync_groups_length);
        for(int i = 0; i < sync_groups_length; i++){
            if(!input_enabled || !input_enabled_groups[i]){
                int group_type = -2;
                for(int j = 0; j < model_count; j++){
                    if(sync_groups[i][j] != -1){
                        if(dm_is_set(GBgetMatrix(models[j], id[j]), RATE, sync_groups[i][j])){
                            group_type = RATE;
                            break;
                        }
                        if(dm_is_set(GBgetMatrix(models[j], id[j]), TAU, sync_groups[i][j])){
                            group_type = TAU;
                            break;
                        }
                        if(dm_is_set(GBgetMatrix(models[j], id[j]), INTERN, sync_groups[i][j])){
                            group_type = INTERN;
                            break;
                        }
                        if(iomapa){
                            if(dm_is_set(GBgetMatrix(models[j], id[j]), INPUT, sync_groups[i][j]) && group_type != OUTPUT){
                                group_type = INPUT;
                            }
                            if(dm_is_set(GBgetMatrix(models[j], id[j]), OUTPUT, sync_groups[i][j])){
                                group_type = OUTPUT;
                                break;
                            }
                        }
                    }
                }
                dm_set(&p_dm_class, group_type, i);
            }
        }
        GBsetMatrix(composition,LTSMIN_EDGE_TYPE_ACTION_CLASS,&p_dm_class,PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_GROUP);
        FILE *classfile = fopen("class.txt", "w+");
        dm_print(classfile, &p_dm_class);
        fclose(classfile);
    }

    //Inhibit matrix
    int inhibit_id = GBgetMatrixID(models[0], "inhibit");
    if(inhibit_id >= 0){
        static matrix_t p_dm_inhibit;
        int inhibit_rows = dm_nrows(GBgetMatrix(models[0], inhibit_id));
        int inhibit_cols = dm_ncols(GBgetMatrix(models[0], inhibit_id));
        dm_create(&p_dm_inhibit, inhibit_rows, inhibit_cols);
        for(int i = 0; i < inhibit_rows; i ++){
            for(int j = 0; j < inhibit_cols; j++){
                if(dm_is_set(GBgetMatrix(models[0], inhibit_id), i, j)){
                    dm_set(&p_dm_inhibit, i, j);
                }
            }
        }
        GBsetMatrix(composition,"inhibit",&p_dm_inhibit,PINS_STRICT,PINS_INDEX_OTHER,PINS_INDEX_OTHER);
    }

    //LTS Type
    lts_type_t ltstype = lts_type_create();
    bool_type=lts_type_put_type(ltstype,"Bool",LTStypeChunk,NULL);
    put_mapa_lts_types(ltstype);
    GBsetLTStype(composition, ltstype);
    GBchunkPutAt(composition,bool_type,chunk_str("F"),0);
    GBchunkPutAt(composition,bool_type,chunk_str("T"),1);

    int len_total = 0;
    int s0_total[lts_type_get_state_length(ltstype)];
    for (int i = 0; i < model_count; i++){
        lts_type_get_state_length (GBgetLTStype(models[i]));
        int len_local = lts_type_get_state_length (GBgetLTStype(models[i]));
        int s0_local[len_local];
        GBgetInitialState(models[i], s0_local);
        for(int j = 0; j < len_local; j++){
            s0_total[j + len_total] = s0_local[j];
        }
        len_total += len_local;
    }

    GBsetInitialState(composition, s0_total);

    //Support copy
    int support_copy = 1;
    for(int i = 0; i < model_count && support_copy; i++){
        support_copy &= GBsupportsCopy(models[i]);
    }
    if(support_copy){
        GBsetSupportsCopy(composition);
    }

}

