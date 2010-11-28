// -*- tab-width:4 ; indent-tabs-mode:nil -*-
#include <config.h>

#include <fnmatch.h>
#include <stdio.h>
#include <string.h>

#include <hre/dir_ops.h>
#include <hre-io/user.h>
#include <string-map.h>

/**************************************************************************/
/* auxiliary functions                                                    */
/**************************************************************************/

typedef struct copy_context {
    archive_t src;
    archive_t dst;
    string_map_t encode;
    int bs;
} *copy_context_t;

static int copy_item(void*arg,int id,char*name){
    (void)id;
    copy_context_t ctx=(copy_context_t)arg;
    Print(info,"copying %s",name);
    char*compression=SSMcall(ctx->encode,name);
    Print(debug,"compression method is %s",compression);
    stream_t is=arch_read(ctx->src,name);
    stream_t os=arch_write_apply(ctx->dst,name,compression);
    char buf[ctx->bs];
    for(;;){
        int len=stream_read_max(is,buf,ctx->bs);
        if (len) stream_write(os,buf,len);
        if(len<ctx->bs) break;
    }
    stream_close(&is);
    stream_close(&os);
    return 0;
}

static void archive_copy(archive_t src,archive_t dst,string_map_t encode,int blocksize,char*pattern){
    struct arch_enum_callbacks cb={.new_item=copy_item};
    struct copy_context ctx;
    ctx.encode=encode;
    ctx.src=src;
    ctx.dst=dst;
    ctx.bs=blocksize;
    arch_enum_t e=arch_enum(src,pattern);
    if (arch_enumerate(e,&cb,&ctx)){
        Abort("unexpected non-zero return");
    }
    arch_enum_free(&e);
}

/**************************************************************************/
/* global variables and options                                           */
/**************************************************************************/

#define GCF_CREATE 1
#define GCF_EXTRACT 2
#define GCF_LIST 3
#define GCF_COPY 4
#define GCF_COMPRESS 5
#define GCF_DECOMPRESS 6

static char* policy="gzip";
static int blocksize=32768;
static int blockcount=32;
static int operation=0;
static int force=0;
static string_map_t compression_policy=NULL;
static char* outputdir=NULL;

static struct poptOption parameters[] = {
    { "force",'f' ,  POPT_ARG_VAL , &force , 1 , "force creation of a directory for output" , NULL },
    { "block-size" , 0 , POPT_ARG_INT|POPT_ARGFLAG_SHOW_DEFAULT , &blocksize , 0 , "set the size of a block in bytes" , "<bytes>" },
    { "cluster-size" , 0 , POPT_ARG_INT|POPT_ARGFLAG_SHOW_DEFAULT , &blockcount , 0 , "set the number of blocks in a cluster" , "<blocks>"},
    { "compression",'z',POPT_ARG_STRING|POPT_ARGFLAG_SHOW_DEFAULT,
        &policy,0,"set the compression policy used in the archive","<policy>"},
    { "output", 'o' , POPT_ARG_STRING , &outputdir , 0, "change the extraction directory" , NULL },
    POPT_TABLEEND
};

static  struct poptOption options[] = {
    { "create", 0 , POPT_ARG_VAL , &operation , GCF_CREATE , "create a new archive" , NULL },
    { "extract", 'x', POPT_ARG_VAL , &operation , GCF_EXTRACT , "extract files from an archive" , NULL },
    { "list",'l', POPT_ARG_VAL , &operation , GCF_LIST , "list the files in the archive" , NULL },
    { "copy" , 0 , POPT_ARG_VAL , &operation , GCF_COPY , "create a new archive by copying an existing archive" , NULL },
    { "compress" , 'c' , POPT_ARG_VAL , &operation , GCF_COMPRESS , "compress all arguments" , NULL},
    { "decompress" , 'd' , POPT_ARG_VAL , &operation , GCF_DECOMPRESS , "decompress all arguments" , NULL},
    { NULL , 0 , POPT_ARG_INCLUDE_TABLE , parameters , 0 , "Parameters", NULL },
    POPT_TABLEEND
};

/**************************************************************************/
/* extract from archive                                                   */
/**************************************************************************/

static void gcf_extract(){
    char *gcf_name=HREnextArg();
    if (gcf_name==NULL) {
        Abort("missing <gcf archive> argument");
    }
    archive_t arch=arch_gcf_read(raf_unistd(gcf_name));
    archive_t dir;
    if (outputdir) {
        dir=arch_dir_create(outputdir,blocksize,force?DELETE_ALL:DELETE_NONE);
    } else {
        dir=arch_dir_open(".",blocksize);
    }
    char*pattern=HREnextArg();
    do {
        archive_copy(arch,dir,NULL,blocksize,pattern);
    } while((pattern=HREnextArg()));
    arch_close(&dir);
    arch_close(&arch);
}

/**************************************************************************/
/* create archive                                                         */
/**************************************************************************/

static void gcf_create(){
    char *gcf_name=HREnextArg();
    if (gcf_name==NULL) {
        Abort("missing <gcf archive> argument");
    }
    archive_t arch=arch_gcf_create(raf_unistd(gcf_name),blocksize,blocksize*blockcount,0,1);
    char*file;
    while((file=HREnextArg())){
        if (is_a_file(file)){
            stream_t is=file_input(file);
            stream_t os=arch_write_apply(arch,file,SSMcall(compression_policy,file));
            char buf[blocksize];
            for(;;){
                int len=stream_read_max(is,buf,blocksize);
                if (len) stream_write(os,buf,len);
                if(len<blocksize) break;
            }
            stream_close(&is);
            stream_close(&os);
        } else {
            Abort("cannot add %s because it is not a file",file);
        }
    }
    arch_close(&arch);
}

/**************************************************************************/
/* copy archive                                                           */
/**************************************************************************/

static void gcf_copy(){
    char* source=HREnextArg();
    if (source==NULL) {
        Abort("missing <source> argument");
    }
    char* target=HREnextArg();
    if (target==NULL) {
        Abort("missing <target> argument");
    }
    if (HREnextArg()){
        Abort("too many arguments");
    }
    archive_t arch_in=arch_gcf_read(raf_unistd(source));
    archive_t arch_out=arch_gcf_create(raf_unistd(target),blocksize,blocksize*blockcount,0,1);
    archive_copy(arch_in,arch_out,compression_policy,blocksize,NULL);
    arch_close(&arch_in);
    arch_close(&arch_out);
}

/**************************************************************************/
/* (de)compress files and directories                                     */
/**************************************************************************/

static void gcf_compress(){
    char*source;
    char target[LTSMIN_PATHNAME_MAX];
    while((source=HREnextArg())){
        if (is_a_file(source)){
            sprintf(target,"%s.gzf",source);
            stream_t is=file_input(source);
            stream_t os=file_output(target);
            char *code=SSMcall(compression_policy,source);
            DSwriteS(os,code);
            os=stream_add_code(os,code);
            char buf[blocksize];
            for(;;){
                int len=stream_read_max(is,buf,blocksize);
                if (len) stream_write(os,buf,len);
                if(len<blocksize) break;
            }
            stream_close(&is);
            stream_close(&os);
            recursive_erase(source);
        } else if (is_a_dir(source)){
            sprintf(target,"%s.gcf",source);
            archive_t arch_in=arch_dir_open(source,blocksize);
            archive_t arch_out=arch_gcf_create(raf_unistd(target),blocksize,blocksize*blockcount,0,1);
            archive_copy(arch_in,arch_out,compression_policy,blocksize,NULL);
            arch_close(&arch_in);
            arch_close(&arch_out);
            recursive_erase(source);
        } else {
            Abort("source %s is neither a file nor a directory",source);
        }
    }
}

static int has_extension(const char*name,const char*extension){
    size_t len=strlen(name);
    return len>strlen(extension) && strcmp(name+(len-4),extension)==0;
}

static void gcf_decompress(){
    char*source;
    char target[LTSMIN_PATHNAME_MAX];
    while((source=HREnextArg())){
        if (has_extension(source,".gzf")){
            strncpy(target,source,strlen(source)-4);
            target[strlen(source)-4]=0;
            stream_t is=file_input(source);
            stream_t os=file_output(target);
            char *code=DSreadSA(is);
            is=stream_add_code(is,code);
            char buf[blocksize];
            for(;;){
                int len=stream_read_max(is,buf,blocksize);
                if (len) stream_write(os,buf,len);
                if(len<blocksize) break;
            }
            stream_close(&is);
            stream_close(&os);
            recursive_erase(source);
        } else if (has_extension(source,".gcf")){
            strncpy(target,source,strlen(source)-4);
            target[strlen(source)-4]=0;
            archive_t arch_in=arch_gcf_read(raf_unistd(source));
            archive_t arch_out=arch_dir_create(target,blocksize,force?DELETE_ALL:DELETE_NONE);
            archive_copy(arch_in,arch_out,NULL,blocksize,NULL);
            arch_close(&arch_in);
            arch_close(&arch_out);
            recursive_erase(source);
        } else {
            Abort("source %s does not have .gzf or .gcf extension",source);
        }
    }
}

/**************************************************************************/
/* list archive                                                           */
/**************************************************************************/

struct list_count {
    uint64_t total_orig;
    uint64_t total_compressed;
    int files;
};

static int list_item(void*arg,int no,archive_item_t item){
    (void)no;
    ((struct list_count*)arg)->files++;
    ((struct list_count*)arg)->total_orig+=item->length;
    ((struct list_count*)arg)->total_compressed+=item->compressed;
    if (item->code==NULL || strlen(item->code)==0) {
        Printf(infoShort,"%12lld %12s %s\n",item->length,"",item->name);
    } else {
        Printf(infoShort,"%12lld %12lld %s (%s)\n",item->length,item->compressed,item->name,item->code);
    }
    return 0;
}

static void gcf_list(){
    char *gcf_name=HREnextArg();
    if (gcf_name==NULL) {
        Abort("missing <gcf archive> argument");
    }
    if (HREnextArg()){
        Abort("too many arguments");
    }
    raf_t raf=raf_unistd(gcf_name);
    archive_t gcf=arch_gcf_read(raf);
    struct arch_enum_callbacks cb={.stat=list_item};
    struct list_count totals={0,0,0};
    Printf(infoShort,"Archive %s contains:\n",gcf_name);
    Printf(infoShort," stream size   compressed stream name (compression)\n",gcf_name);
    arch_enum_t e=arch_enum(gcf,NULL);
    if (arch_enumerate(e,&cb,&totals)){
        Abort("unexpected non-zero return");
    }
    Printf(infoShort,"totals:\n");
    Printf(infoShort,"%12lld %12lld files: %d (%3.2f%%)\n",
        totals.total_orig,totals.total_compressed,totals.files,
        100.0*((float)(totals.total_orig-totals.total_compressed))/((float)totals.total_orig));
    arch_enum_free(&e);
    uint64_t gcf_size=raf_size(raf);
    Printf(infoShort,"gcf file size%12llu (%3.2f%% overhead, %3.2f%% compression)\n",gcf_size,
        100.0*((float)(gcf_size-totals.total_compressed))/((float)totals.total_compressed),
        100.0*(((float)totals.total_orig)-((float)gcf_size))/((float)totals.total_orig));
    arch_close(&gcf);
}

/**************************************************************************/
/* main                                                                   */
/**************************************************************************/

int main(int argc, char *argv[]){
    HREinitBegin(argv[0]);
    HREaddOptions(options,"Tool for creating and extracting GCF archives\n\nOptions");
    HREinitStart(&argc,&argv,0,-1,NULL,"<operation> <arguments>");
    compression_policy=SSMcreateSWP(policy);
    switch(operation){
    case GCF_CREATE:
        gcf_create();
        break;
    case GCF_EXTRACT:
        gcf_extract();
        break;
     case GCF_LIST:
        gcf_list();
        break;
    case GCF_COPY:
        gcf_copy();
        break;
    case GCF_COMPRESS:
        gcf_compress();
        break;
    case GCF_DECOMPRESS:
        gcf_decompress();
        break;
    default:
        Abort("unknown operation %d",operation);
    }
    HREexit(EXIT_SUCCESS);
}

