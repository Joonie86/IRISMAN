/*
    (c) 2011-2013 Hermes/Estwald <www.elotrolado.net>
    IrisManager (HMANAGER port) (c) 2011 D_Skywalk <http://david.dantoine.org>

    HMANAGER4 is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    HMANAGER4 is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with HMANAGER4.  If not, see <http://www.gnu.org/licenses/>.
*/
#include "loader.h"

#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <math.h>

#include <sysutil/osk.h>
#include "sysutil/sysutil.h"
#include <sys/memory.h>
#include <ppu-lv2.h>
#include <sys/stat.h>

#include <sys/file.h>
#include <lv2/sysfs.h>

#include "file_manager.h"
#include "main.h"
#include "gfx.h"
#include "pad.h"
#include "ttf_render.h"
#include "utils.h"
#include "osk_input.h"

#include <matrix.h>

#include "cobra.h"
#include "iso.h"
#include "ftp/ftp.h"
#include "ftp/functions.h"
#include "modules.h"
#include "psx.h"

#define INITED_CALLBACK     1
#define INITED_SPU          2
#define INITED_SOUNDLIB     4
#define INITED_AUDIOPLAYER  8

#include <spu_soundlib.h>
#include <audioplayer.h>

void draw_device_mkiso(float x, float y, int index, char *path);
void load_background_picture();

#define MAX_SECTIONS    ((0x10000-sizeof(rawseciso_args))/8)

#define ROT_INC(x ,y , z) {x++; if(x > y) x = z;}
#define ROT_DEC(x ,y , z) {x--; if(x < y) x = z;}

typedef struct
{
    uint64_t device;
    uint32_t emu_mode;
    uint32_t num_sections;
    uint32_t num_tracks;
    // sections after
    // sizes after
    // tracks after
} __attribute__((packed)) rawseciso_args;

extern u32 snd_inited;
extern u32 spu;

extern int noBDVD;

extern bool use_cobra;
extern bool use_mamba;

extern bool bAllowNetGames;

extern int menu_screen;
extern bool set_install_pkg;

extern bool options_locked;
extern char psp_launcher_path[MAXPATHLEN];
extern char retroarch_path[MAXPATHLEN];

extern char browser_extensions[100];
extern char rom_extensions[300];
extern char retro_root_path[ROMS_MAXPATHLEN];
extern char retro_snes_path[ROMS_MAXPATHLEN];
extern char retro_gba_path[ROMS_MAXPATHLEN];
extern char retro_gen_path[ROMS_MAXPATHLEN];
extern char retro_nes_path[ROMS_MAXPATHLEN];
extern char retro_mame_path[ROMS_MAXPATHLEN];
extern char retro_fba_path[ROMS_MAXPATHLEN];
extern char retro_doom_path[ROMS_MAXPATHLEN];
extern char retro_quake_path[ROMS_MAXPATHLEN];
extern char retro_pce_path[ROMS_MAXPATHLEN];
extern char retro_gb_path[ROMS_MAXPATHLEN];
extern char retro_gbc_path[ROMS_MAXPATHLEN];
extern char retro_atari_path[ROMS_MAXPATHLEN];
extern char retro_vb_path[ROMS_MAXPATHLEN];
extern char retro_nxe_path[ROMS_MAXPATHLEN];
extern char retro_wswan_path[ROMS_MAXPATHLEN];

char rom_extension[10];

extern int num_box;
extern int bk_picture;

#define TEMP_PICT num_box + 1

#define FS_S_IFMT 0170000
#define FS_S_IFDIR 0040000

#define BLACK       0x000000ff
#define WHITE       0xffffffff
#define RED1        0xff0000ff
#define BLUE1       0x00001080 // 0x0040ff80
#define BLUE2       0x04244280 // 0x0070ff80
#define BLUE3       0x000010FF // 0x0060ff80
#define BLUE4       0x042442FF // 0x0080ff80
#define BLUE5       0x0f3b7d80 // 0x20a0a8ff
#define BLUE6       0x40c0ffff
#define GRAY        0x8f8f8fff
#define GREEN       0x8fff00ff
#define CYAN        0x00ffffff
#define CYAN2       0x00AAAA80
#define MAGENTA     0xC000C0FF
#define YELLOW      0x8f8f00ff // dark yellow
#define YELLOW2     0xffff00ff // bright yellow
#define INVISIBLE   0x00000000
#define CURSORCOLOR 0x062662FF
#define POPUPMENUCOLOR 0x04244280

#define BLINK       0x10
#define BLINK_SLOW  0x20

#define MOVIAN   "/dev_hdd0/game/HTSS00003/USRDIR/movian.self"
#define SHOWTIME "/dev_hdd0/game/HTSS00003/USRDIR/showtime.self"


////////////////
int pos1 = 0;
int pos2 = 0;

int sel1 = 0;
int sel2 = 0;

#define MAX_PATH_LEN   0x420

#ifndef LOADER_MODE

static int audio_pane = 0;

static char audio_file[MAX_PATH_LEN];

static char path1[MAX_PATH_LEN];
static char path2[MAX_PATH_LEN];

static bool update_devices1 = false;
static bool update_devices2 = false;

static int update_device_sizes = 1|2; // flags to update the free device space calling to the function (1-> win1  | 2 -> win2)

char hex_path[MAX_PATH_LEN];

u64 hex_filesize = 0;

#define MAX_ENTRIES 2048

sysFSDirent entries1[MAX_ENTRIES];
sysFSDirent entries2[MAX_ENTRIES];

int entries1_type[MAX_ENTRIES];
int entries2_type[MAX_ENTRIES];

s64 entries1_size[MAX_ENTRIES];
s64 entries2_size[MAX_ENTRIES];

int nentries1, nentries2;
int selcount1, selcount2;
s64 selsize1, selsize2;

#endif

MATRIX mat_unit, mat_win1, mat_win2;

u32 frame = 300;
int fm_pane = 0;

bool is_vsplit;

int set_menu2 = 0;

int change_path1 = 0, change_path2 = 0;

sysFSStat stat1;
sysFSStat stat2;

u64 free_device1 = 0ULL;
u64 free_device2 = 0ULL;
////////////////

u64 pos = 0;
u64 readed = 0;
int e_x = 0, e_y = 0;

#define MSG_HOW_TO_UNMOUNT_DEVICE  " (USB_00%i) Press SELECT + [] to Unmount USB device"

////////////////

int LoadTexturePNG(char * filename, int index);
int LoadTextureJPG(char * filename, int index);

u64 syscall_40(u64 cmd, u64 arg);

extern char temp_buffer[8192];
extern int firmware;
extern char self_path[MAXPATHLEN];

#define HEX_EDIT        0x1C00
#define HEX_READ        0x1E00

#define MEM_MESSAGE_OFFSET  0x400
#define TEMP_PATH_OFFSET    0x1000
#define TEMP_PATH1_OFFSET   0x1400
#define TEMP_PATH2_OFFSET   0x1800

#define MEM_MESSAGE     temp_buffer + MEM_MESSAGE_OFFSET
#define TEMP_PATH       temp_buffer + TEMP_PATH_OFFSET
#define TEMP_PATH1      temp_buffer + TEMP_PATH1_OFFSET
#define TEMP_PATH2      temp_buffer + TEMP_PATH2_OFFSET
#define MEM_HEX_EDIT    temp_buffer + HEX_EDIT   //0X180
#define MEM_HEX_READ    temp_buffer + HEX_READ   //0X180

int mnt_mode = 1; // 0 = Mount NTFS file as fake ISO, 1 = Mount and exit to XMB

int mount_option = 0;
bool allow_shadow_copy = true;

int exit_option = 0; // 0 = Exit File Manager, 1 = Exit to XMB, 2 = Restart the PS3

int sys_map_path(char *oldpath, char *newpath);
int mount_psp_iso(char *path);

int sys_fs_mount(char const* deviceName, char const* deviceFileSystem, char const* devicePath, int writeProt);
int sys_fs_umount(char const* devicePath);

//void MSGBOX(char *text, char *text2) {sprintf(MEM_MESSAGE, "%s = %s", text, text2); DrawDialogOKTimer(MEM_MESSAGE, 3000.0f);}    //debug message
//void MSGBOX2(char *text, int i) {sprintf(MEM_MESSAGE, "%s = %i", text, i); DrawDialogOKTimer(MEM_MESSAGE, 5000.0f);}    //debug message

char * getlv2error(s32 error)
{
    switch(error)
    {
        case 0x00000000:
            return "Ok";
        case 0x80010001:
            return "The resource is temporarily unavailable";
        case 0x80010002:
            return "Invalid argument";
        case 0x80010003:
            return "Function not implemented";
        case 0x80010004:
            return "Memory allocation failed";
        case 0x80010005:
            return "No such process";
        case 0x80010006:
            return "No such file or directory";
        case 0x80010007:
            return "Exec format error";
        case 0x80010008:
            return "Deadlock condition";
        case 0x80010009:
            return "Operation not permitted";
        case 0x8001000A:
            return "Device busy";
        case 0x8001000B:
            return "The operation is timed out";
        case 0x8001000C:
            return "The operation is aborted ";
        case 0x8001000D:
            return "Invalid memory access";
        case 0x80010012:
            return "The file is a directory";
        case 0x80010013:
            return "Operation canceled";
        case 0x80010014:
            return "File exists";
        case 0x80010015:
            return "Socket is already connected";
        case 0x80010016:
            return "Socket is not connected";
        case 0x8001001B:
            return "Math arg out of domain of func";
        case 0x8001001C:
            return "Math result not representable";
        case 0x8001001D:
            return "Illegal multi-byte sequence in input";
        case 0x8001001E:
            return "File position error";
        case 0x8001001F:
            return "Syscall was interrupted";
        case 0x80010020:
            return "File too large";
        case 0x80010021:
            return "Too many links";
        case 0x80010022:
            return "Too many open files in system";
        case 0x80010023:
            return "No space left on device";
        case 0x80010024:
            return "Not a typewriter";
        case 0x80010025:
            return "Broken pipe";
        case 0x80010026:
            return "Read only file system";
        case 0x80010027:
            return "Illegal seek";
        case 0x80010029:
            return "Permission denied";
        case 0x8001002A:
            return "Invalid file descriptor";
        case 0x8001002B:
            return "I/O error";
        case 0x8001002C:
            return "Too many open files";
        case 0x8001002D:
            return "No such device";
        case 0x8001002E:
            return "Not a directory";
        case 0x8001002F:
            return "No such device or address";
        case 0x80010030:
            return "Cross-device link";
        case 0x80010031:
            return "Trying to read unreadable message";
        case 0x80010032:
            return "Connection already in progress";
        case 0x80010033:
            return "Message too long";
        case 0x80010034:
            return "File or path name too long";
        case 0x80010035:
            return "No record locks available";
        case 0x80010036:
            return "Directory not empty";
        case 0x80010037:
            return "Not supported";
        case 0x80010039:
            return "Value too large for defined data type";
        case 0x8001003A:
            return "Filesystem not mounted";

        default:
            return "Error Unknown";
    }
}

/***********************************************************************************************************/
/* NTFS                                                                                                    */
/***********************************************************************************************************/

const DISC_INTERFACE *disc_ntfs[8]= {
    &__io_ntfs_usb000,
    &__io_ntfs_usb001,
    &__io_ntfs_usb002,
    &__io_ntfs_usb003,
    &__io_ntfs_usb004,
    &__io_ntfs_usb005,
    &__io_ntfs_usb006,
    &__io_ntfs_usb007
};

// mounts from /dev_usb000 to 007
ntfs_md *mounts[8] = {NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL};
int mountCount[8] = {0, 0, 0, 0, 0, 0, 0, 0};
int automountCount[8] = {0, 0, 0, 0, 0, 0, 0, 0};


u32 ports_cnt = 0;
u32 old_ports_cnt = 0;
int ntfs_mount_delay = 2;

int NTFS_Event_Mount(int id)
{
    int r = 0;

    ports_cnt &= ~(1<<id);
    if(PS3_NTFS_IsInserted(id)) ports_cnt |= 1<<id;

    if( ((ports_cnt>>id) & 1) && !((old_ports_cnt>>id) & 1)) automountCount[id] = ntfs_mount_delay; // enable delay event

    if(automountCount[id] > 0)
    {   // if delay counter ticks...
        automountCount[id]--; if(automountCount[id] == 0) {r = NTFS_DEVICE_MOUNT; ntfs_mount_delay = (7 * 60);}// mount device (7 seconds)
    }

    if( !((ports_cnt>>id) & 1) && ((old_ports_cnt>>id) & 1))
    {   // unmount device
        automountCount[id] = 0; r = NTFS_DEVICE_UNMOUNT;
    }

    old_ports_cnt = ports_cnt;

    return r;
}

int NTFS_UnMount(int id)
{
    int ret = 0;

    if (mounts[id])
    {
        int k;
        for (k = 0; k < mountCount[id]; k++)
            if((mounts[id]+k)->name[0])
                {ret = NTFS_DEVICE_UNMOUNT; ntfsUnmount((mounts[id]+k)->name, true); (mounts[id]+k)->name[0] = 0;}

        free(mounts[id]);
        mounts[id]= NULL;
        mountCount[id] = 0;
    }

    PS3_NTFS_Shutdown(id);

    return ret;
}

void NTFS_UnMountAll(void)
{
    int i;

    for(i = 0; i < 8; i++)
    {
        NTFS_UnMount(i);
    }
}

int NTFS_Test_Device(char *name)
{
    int k, i;

    for(k = 0; k < 8; k++)
    {
        for (i = 0; i < mountCount[k]; i++)
        if(!strncmp((mounts[k]+i)->name, name, 5 - ((mounts[k]+i)->name[0] == 'e')))
            return ((mounts[k] + i)->interface->ioType & 0xff) - '0';
    }

    return NTFS_DEVICE_UNMOUNT;
}


/***********************************************************************************************************/
/* msgDialog                                                                                               */
/***********************************************************************************************************/


static msgType mdialogprogress =   MSG_DIALOG_SINGLE_PROGRESSBAR | MSG_DIALOG_MUTE_ON;
static msgType mdialogprogress2 =   MSG_DIALOG_DOUBLE_PROGRESSBAR | MSG_DIALOG_MUTE_ON;

static volatile int progress_action = 0;

void init_music(int select_song);

void test_audio_file(bool stop_audio)
{
    sysUtilCheckCallback();
    if((snd_inited & INITED_AUDIOPLAYER) && (StatusAudio()==AUDIO_STATUS_EOF || StatusAudio()==AUDIO_STATUS_ERR || stop_audio))
    {
        StopAudio(); snd_inited &= ~INITED_AUDIOPLAYER; audio_file[0] = 0;

        bool exit_loop = false; if(stop_audio) return;

        if(audio_pane == 0) {init_music(-1); return;}

        if(audio_pane == 1 && selcount1<1)
        {
            while(sel1<nentries1)
            {
                sel1++; if(sel1>=nentries1) {sel1=0; if(exit_loop) break; else exit_loop=true;}
                sprintf(audio_file, "%s/%s", path1, entries1[sel1].d_name);
                if(strcasestr(entries1[sel1].d_name, ".mp3") || strcasestr(entries1[sel1].d_name, ".ogg")) break;
            }
        }
        if(audio_pane == 2 && selcount2<1)
        {
            while(sel2<nentries2)
            {
                sel2++; if(sel2>=nentries2) {sel2=0; if(exit_loop) break; else exit_loop=true;}
                sprintf(audio_file, "%s/%s", path2, entries2[sel2].d_name);
                if(strcasestr(entries2[sel2].d_name, ".mp3") || strcasestr(entries2[sel2].d_name, ".ogg")) break;
            }
        }

        if(PlayAudio(audio_file, 0, AUDIO_ONE_TIME)==0) snd_inited|= INITED_AUDIOPLAYER;
    }
}
static void progress_callback(msgButton button, void *userdata)
{
    switch(button)
    {
        case MSG_DIALOG_BTN_OK:
            progress_action = 1;
            break;
        case MSG_DIALOG_BTN_NO:
        case MSG_DIALOG_BTN_ESCAPE:
            progress_action = 2;
            break;
        case MSG_DIALOG_BTN_NONE:
            progress_action = -1;
            break;
        default:

            break;
    }
}


static void update_bar(u32 cpart)
{
    msgDialogProgressBarInc(MSG_PROGRESSBAR_INDEX0, (u32) cpart);
    sysUtilCheckCallback(); tiny3d_Flip();
}

static void update_bar2(u32 cpart)
{
    msgDialogProgressBarInc(MSG_PROGRESSBAR_INDEX1, (u32) cpart);
    sysUtilCheckCallback(); tiny3d_Flip();
}

static void single_bar(char *caption)
{
    progress_action = 0;

    msgDialogOpen2(mdialogprogress, caption, progress_callback, (void *) 0xadef0044, NULL);

    msgDialogProgressBarReset(MSG_PROGRESSBAR_INDEX0);

    sysUtilCheckCallback();tiny3d_Flip();
}

static int Files_To_Copy = 0;
static int Folders_To_Copy = 0;

static float progress_0 = 0.0f;

static void double_bar(char *caption)
{
    progress_action = 0;

    msgDialogOpen2(mdialogprogress2, caption, progress_callback, (void *) 0xadef0042, NULL);

    msgDialogProgressBarReset(MSG_PROGRESSBAR_INDEX0);
    msgDialogProgressBarReset(MSG_PROGRESSBAR_INDEX1);

    progress_0 = 0.0f;
    sysUtilCheckCallback();tiny3d_Flip();
}

void DrawBox2(float x, float y, float z, float w, float h)
{
    tiny3d_SetPolygon(TINY3D_QUADS);

    tiny3d_VertexPos(x    , y    , z);
    tiny3d_VertexColor(BLUE1);

    tiny3d_VertexPos(x + w, y    , z);
    tiny3d_VertexColor(BLUE2);

    tiny3d_VertexPos(x + w, y + h, z);
    tiny3d_VertexColor(BLUE3);

    tiny3d_VertexPos(x    , y + h, z);
    tiny3d_VertexColor(BLUE4);

    tiny3d_End();
}

#ifndef LOADER_MODE
static int entry_compare(const void *va, const void *vb)
{
    sysFSDirent * a =  (sysFSDirent *) va;
    sysFSDirent * b =  (sysFSDirent *) vb;

    if((a->d_type & IS_DIRECTORY) >  (b->d_type & IS_DIRECTORY) ||
      ((a->d_type & IS_DIRECTORY) == (b->d_type & IS_DIRECTORY) && strcmp(a->d_name, b->d_name) < 0) ||
      !strcmp(a->d_name, ".."))
        return -1;
    else
        return 1;
}

static bool test_mark_flags(sysFSDirent *ent, int nent, int *nmarked)
{
    int n;
    bool ret = false;
    *nmarked = 0;
    for(n = 0; n < nent; n++)
        if(ent[n].d_type & IS_MARKED) {ret = true; (*nmarked) ++;}
    return ret;
}
#endif

static int reset_copy = 1;

static char *cpy_str = "Copy";

static char *dyn_get_name(char *p)
{
    int n = strlen(p); while(n > 0 && p[n] != '/') n--;
    return &p[n+1];
}

static int CountFiles(char* path, int *nfiles, int *nfolders, u64 *size)
{
    int dfd;
    u64 read;
    sysFSDirent dir;
    int ret = 0;
    int p1 = strlen(path);
    DIR_ITER *pdir = NULL;
    struct stat st;
    bool is_ntfs = is_ntfs_path(path);

    if(is_ntfs)
    {
        ret = ps3ntfs_stat(path, &st);
        if (ret < 0) return ret;

        ret = 0;
        (*size)+= st.st_size;
    }
    else
    {
        sysFSStat stat;

        ret = sysLv2FsStat(path, &stat);
        if (ret < 0) return ret;

        (*size)+= stat.st_size;

    }


    if(is_ntfs)
    {
        pdir = ps3ntfs_diropen(path);
        if(pdir) ret = SUCCESS; else ret = FAILED;
    }
    else
        ret = sysLv2FsOpenDir(path, &dfd);

    if(ret) return ret;

    read = sizeof(sysFSDirent);
    while ((!is_ntfs && !sysLv2FsReadDir(dfd, &dir, &read)) ||
           ( is_ntfs &&  ps3ntfs_dirnext(pdir, dir.d_name, &st) == SUCCESS))
    {
        if (!is_ntfs && !read)
            break;
        if (!strcmp(dir.d_name, ".") || !strcmp(dir.d_name, ".."))
            continue;

        path[p1]= 0;

        strcat(path, "/");
        strcat(path, dir.d_name);

        if(!is_ntfs)
        {
            if(dir.d_type & IS_DIRECTORY)
            {
                (*nfolders) ++;

                ret = CountFiles(path, nfiles, nfolders, size);
                if(ret) goto skip;
            }
            else
            {
                sysFSStat stat;

                ret = sysLv2FsStat(path, &stat);
                if(ret < 0) goto skip;

                (*size) += stat.st_size;
                (*nfiles) ++;
            }
        }
        else
        {
            if(S_ISDIR(st.st_mode))
            {
                (*nfolders) ++;

                ret = CountFiles(path, nfiles, nfolders, size);
                if(ret) goto skip;
            }
            else
            {
                ret = ps3ntfs_stat(path, &st);
                if (ret < 0) goto skip;

                (*size) += st.st_size;
                (*nfiles) ++;
            }
        }
    }

skip:

    path[p1]= 0;
    if(is_ntfs) ps3ntfs_dirclose(pdir); else sysLv2FsCloseDir(dfd);

    return ret;
}

u64 get_free_space(char * path, bool usecache)
{
    int i;
    static u64 cached_freeSize[20];
    static int cached_pathHash[20];

    if(!path || path[1] == 0 || path[1] == 'a' || path[1] == 'h' || (path[5] == 'b' && path[6] == 'd')) return 0; //NULL, /, app_home, host_root, /dev_bdvd

    u32 blockSize;
    u64 freeSize = 0;

    //get device name ending with slash e.g. /dev_hdd0/
    int n = 1; while(path[n] != '/' && path[n] != 0) n++;
    memcpy(temp_buffer, path, n);
    temp_buffer[n] = '/';
    temp_buffer[n + 1]=0;

    int hash = 0;
    for(i = strlen(temp_buffer); i >= 0; i--) hash += temp_buffer[i];

    if(usecache)
    {
        for(i = 0; i < 20; i++)
            if(cached_pathHash[i] == hash && cached_freeSize[i]) return cached_freeSize[i];
    }
    else
        for(i = 0; i < 20; i++)
            if(cached_pathHash[i] == hash) {cached_freeSize[i] = cached_pathHash[i] = 0; break;}

    if(!is_ntfs_path(temp_buffer))
    {
        sysFsGetFreeSize(temp_buffer, &blockSize, &freeSize);

        freeSize = (((u64)blockSize * freeSize));
    }
    else
    {
        struct statvfs vfs;
        ps3ntfs_statvfs(temp_buffer, &vfs);

        freeSize = (((u64)vfs.f_bsize * vfs.f_bfree));
    }

    for(i = 0; i<20; i++)
        if(!cached_pathHash[i])
        {
            cached_pathHash[i] = hash;
            cached_freeSize[i] = freeSize;

            return freeSize;
        }

    if(i >= 20) //rotate cached values
    {
        for(i = 19; i > 0; i--)
        {
           cached_pathHash[i] = cached_pathHash[i-1];
           cached_freeSize[i] = cached_freeSize[i-1];
        }

        cached_pathHash[i] = hash;
        cached_freeSize[i] = freeSize;
    }

    return freeSize;
}

extern u64 lv2peek(u64 addr);
extern u64 lv2poke(u64 addr, u64 value);

static int level_dump(char *path, u64 size, int mode)
{
    if(get_free_space(path, false) < size) return (int) 0x80010020;

    int ret = 0;
    int n;
    s32 fd = FAILED;

    time_t timer;
    struct tm * timed;

    bool is_ntfs = is_ntfs_path(path);

    time(&timer);
    timed = localtime(&timer);

    if(firmware < 0x421C && mode == 1) return (int) 0x80010009;

    u64 *mem = NULL;

    if(mode == 1)
    {
        // LV1
        mem = (u64 *) malloc(0x1000000);
        if(!mem) return (int) 0x80010004;

        DrawDialogTimer("Dumping LV1 ...", 1200.0f);

        memset((void *) mem, 0, 0x1000000);

        lv1_reg regs_i, regs_o;

        memset(&regs_i, 0, sizeof(regs_i));
/*
        regs_i.reg11 = 0xB6;
        sys8_lv1_syscall(&regs_i, &regs_o);

        if(((int) regs_o.reg3) <0) {
            return  (int) 0x80010004;
        }
*/
        single_bar("LV1 Dump process");

        for(n = 0; n < 0x1000000/8; n++)
        {
            regs_i.reg11 = 0xB6; regs_i.reg3 = (u64) (n<<3);
            sys8_lv1_syscall(&regs_i, &regs_o);
            mem[n] = regs_o.reg4;
        }

        sprintf(temp_buffer, "%s/LV1-%XEX-%04i%02i%02i-%02i%02i%02i.bin", path, firmware,
            timed->tm_year+1900, timed->tm_mon+1,  timed->tm_mday, timed->tm_hour, timed->tm_min, timed->tm_sec);

        if(is_ntfs)
            {fd = ps3ntfs_open(temp_buffer, O_WRONLY | O_CREAT | O_TRUNC, 0);if(fd < 0) ret = FAILED; else ret = SUCCESS;}
        else
            ret = sysLv2FsOpen(temp_buffer, SYS_O_WRONLY | SYS_O_CREAT | SYS_O_TRUNC, &fd, 0777, NULL, 0);

        if(ret < 0) goto skip;
        if(!is_ntfs) sysLv2FsChmod(temp_buffer, FS_S_IFMT | 0777);

    }
    else
    {
        // LV2
        mem = (u64 *) malloc(0x800000);
        if(!mem) return (int) 0x80010004;

        memset((void *) mem, 0, 0x800000);

        single_bar("LV2 Dump process");

        for(n = 0; n < 0x800000/8; n++) mem[n]= lv2peek(0x8000000000000000ULL + (u64)(n<<3));

        sprintf(temp_buffer, "%s/LV2-%XEX-%04i%02i%02i-%02i%02i%02i.bin", path, firmware,
            timed->tm_year+1900, timed->tm_mon+1,  timed->tm_mday, timed->tm_hour, timed->tm_min, timed->tm_sec);

        if(is_ntfs)
            {fd = ps3ntfs_open(temp_buffer, O_WRONLY | O_CREAT | O_TRUNC, 0);if(fd < 0) ret = FAILED; else ret = SUCCESS;}
        else
            ret = sysLv2FsOpen(temp_buffer, SYS_O_WRONLY | SYS_O_CREAT | SYS_O_TRUNC, &fd, 0777, NULL, 0);

        if(ret < 0) goto skip;
        if(!is_ntfs) sysLv2FsChmod(temp_buffer, FS_S_IFMT | 0777);
    }

    u64 pos = 0ULL;
    u64 readed = 0, writed = 0;
    u64 length = 0x800000ULL;

    if(mode == 1) length = 0x1000000ULL;

    float parts = (length == 0) ? 0.0f : 100.0f / ((double) length / (double) 0x100000);
    float cpart = 0;

    while(pos < length)
    {
        readed = length - pos; if(readed > 0x100000ULL) readed = 0x100000ULL;

        if(is_ntfs)
           {ret = ps3ntfs_write(fd, (void *) &mem[pos>>3], (int) readed); writed = (u64) ret; if(ret > 0) ret = 0;}
        else
            ret = sysLv2FsWrite(fd, &mem[pos>>3], readed, &writed);

        if(ret < 0) goto skip;
        if(readed != writed) {ret = 0x8001000C; goto skip;}

        pos += readed;

        if(progress_action == 2) {ret = 0x8001000C; goto skip;}

        cpart += parts;
        if(cpart >= 1.0f) {
            update_bar((u32) cpart);
            cpart-= (float) ((u32) cpart);
        }
    }

skip:
    if(fd >= SUCCESS) {if(is_ntfs) ps3ntfs_close(fd); else sysLv2FsClose(fd);}
    if(ret > SUCCESS) ret = SUCCESS;
    if(mem) free(mem);

    if(progress_action == 2) unlink_secure(temp_buffer);

    msgDialogAbort();

    if(file_exists(temp_buffer))
    {
        char msg[100];
        sprintf(msg, "%s has been created!", temp_buffer);
        DrawDialogOKTimer(msg, 5000.0f);
    }

    return ret;
}

static  float copy_parts;
static float copy_cpart;

#include "event_threads.h"

static int use_async_fd = 0;

volatile struct f_async {
    int flags;
    int fd;
    void * mem;
    int size;
    u64 readed;
} my_f_async;

#define ASYNC_ENABLE 128
#define ASYNC_ERROR 16
#define ASYNC_FCLOSE 2
#define ASYNC_NTFS 1

static void my_func_async(struct f_async * v)
{
    int ret = FAILED;

    if(v && v->flags & ASYNC_ENABLE)
    {
        v->readed = 0;
        int flags = v->flags;
        if(v->mem)
        {
            if(flags & ASYNC_NTFS)
                {ret = ps3ntfs_write(v->fd, v->mem, v->size); v->readed = (u64) ret; if(ret>0) ret = 0;}
            else ret =sysLv2FsWrite(v->fd, v->mem, v->size, &v->readed);

            free(v->mem); v->mem = 0;

            if(ret == 0 && v->size != v->readed) ret = FAILED;
        }

        if(ret) flags|= ASYNC_ERROR;

        if(flags & (ASYNC_ERROR | ASYNC_FCLOSE))
        {
            if(flags & ASYNC_NTFS) ps3ntfs_close(v->fd); else sysLv2FsClose(v->fd);
        }

        flags &= ~ASYNC_ENABLE;

        v->flags = flags;
    }
}

#define CPY_NOTCLOSE 256
#define CPY_FILE1_IS_NTFS 1
#define CPY_FILE2_IS_NTFS 2

static int CopyFd(s32 flags, s32 fd, s32 fd2, char *mem, u64 length)
{
    int ret = 0;
    int one = 0;
    u64 pos = 0ULL;
    u64 readed = 0, writed = 0;

    while(pos < length)
    {
        readed = length - pos; if(readed > 0x100000ULL) readed = 0x100000ULL;

        if(flags & CPY_FILE1_IS_NTFS) {ret = ps3ntfs_read(fd, mem, readed); writed = (u64) ret; if(ret>0) ret = 0;}
        else ret =sysLv2FsRead(fd, mem, readed, &writed);

        if(ret < 0) goto skip;
        if(readed != writed) {ret = 0x8001000C; goto skip;}

        loop_write:

        if(use_async_fd)
        {
            if(use_async_fd == ASYNC_ENABLE)
            {
                use_async_fd = 1;
                my_f_async.flags = 0;
                my_f_async.fd = fd2;
                my_f_async.mem = malloc(readed);
                if(my_f_async.mem) memcpy(my_f_async.mem, mem, readed);
                my_f_async.size = readed;
                my_f_async.readed = 0;
                my_f_async.flags = ASYNC_ENABLE | ((flags & CPY_FILE2_IS_NTFS) != 0)
                    | (ASYNC_FCLOSE * (pos + readed >= length  && !(flags & CPY_NOTCLOSE)));
                event_thread_send(0x555ULL, (u64) my_func_async, (u64) &my_f_async);
            }
            else
            {
                if(!(my_f_async.flags & ASYNC_ENABLE))
                {
                    if(my_f_async.flags & ASYNC_ERROR) {ret = 0x8001000C; goto skip;}
                    my_f_async.flags = 0;
                    my_f_async.fd = fd2;
                    my_f_async.mem = malloc(readed);
                    if(my_f_async.mem) memcpy(my_f_async.mem, mem, readed);
                    my_f_async.size = readed;
                    my_f_async.readed = 0;
                    my_f_async.flags = ASYNC_ENABLE | ((flags & CPY_FILE2_IS_NTFS) != 0)
                        | (ASYNC_FCLOSE * (pos + readed >= length && !(flags & CPY_NOTCLOSE)));
                    event_thread_send(0x555ULL, (u64) my_func_async, (u64) &my_f_async);

                }
                else
                {
                    //wait_event_thread();
                    goto loop_write;
                }
            }

        }
        else
        {
            if(flags & CPY_FILE2_IS_NTFS) {ret = ps3ntfs_write(fd2, mem, readed); writed = (u64) ret; if(ret>0) ret = 0;}
            else ret = sysLv2FsWrite(fd2, mem, readed, &writed);
            if(ret < 0) goto skip;
            if(readed != writed) {ret = 0x8001000C; goto skip;}
        }

        pos += readed;

        if(progress_action == 2) {ret = 0x8001000C; goto skip;}

        copy_cpart += copy_parts;
        if(copy_cpart >= 1.0f)
        {
            one= 1;
            update_bar2((u32) copy_cpart);
            copy_cpart-= (float) ((u32) copy_cpart);
        }

    }

    if(!one) update_bar2((u32) 100.0f);

skip:
    return ret;
}

static int use_iso_splits = 0;

int CopyFile(char* path, char* path2)
{
    int ret = 0;
    s32 fd = FAILED;
    s32 fd2 = FAILED;
    u64 length = 0LL;

    char *mem = NULL;

    sysFSStat stat;
    struct stat fstat;

    s32 flags = 0;

    if(is_ntfs_path(path )) flags|= CPY_FILE1_IS_NTFS;
    if(is_ntfs_path(path2)) flags|= CPY_FILE2_IS_NTFS;

    if(allow_shadow_copy && !strncmp(path, "/dev_hdd0", 9) && !strncmp(path2, "/dev_hdd0", 9))
    {
        sysLv2FsUnlink(path2);
        return sysLv2FsLink(path, path2);
    }

    if(Files_To_Copy == 0) Files_To_Copy = 1;

    progress_0 += 100.0f / (float) Files_To_Copy;
    if(progress_0 >= 1.0f)
    {
        msgDialogProgressBarInc(MSG_PROGRESSBAR_INDEX0, (u32) progress_0);
        progress_0-= (float) ((u32) (100.0f/(float) Files_To_Copy));
    }

    msgDialogProgressBarSetMsg(MSG_PROGRESSBAR_INDEX0, "Progress");
    msgDialogProgressBarReset(MSG_PROGRESSBAR_INDEX1);
    msgDialogProgressBarSetMsg(MSG_PROGRESSBAR_INDEX1, dyn_get_name(path));

    if(reset_copy)
    {
        reset_copy = 0;

        for(ret =0; ret < 20; ret++)
        {
            sysUtilCheckCallback();tiny3d_Flip();
        }
    }

    char *ext = get_extension(path);
    char *ext0 = path;

    while(use_iso_splits)
    {
        char *e = strstr(ext0, ".iso.");
        if(!e) e = strstr(ext0, ".ISO.");
        if(!e) break;
        ext0 = e + 4;
    }

    if(use_iso_splits && strlen(path) > 6 && strncasecmp(ext0 - 4, ".iso.", 5) == SUCCESS)
    {
        // split files
        if(strcmp(ext0, ".0")) goto skip;

        int n;

        fd = fd2 = FAILED;

        mem = malloc(0x100000);
        if(!mem) {ret = (int) 0x80010004; goto skip2;}

        char *ext2 = get_extension(path2);

        if(!strncmp(ext2, ".0", 2)) ext2[0]=0;

        for(n = 0; n < 99; n++)
        {
            fd = FAILED;

            sprintf(ext0, ".%i", n);


            msgDialogProgressBarReset(MSG_PROGRESSBAR_INDEX1);
            msgDialogProgressBarSetMsg(MSG_PROGRESSBAR_INDEX1, dyn_get_name(path2));

            if(flags & CPY_FILE1_IS_NTFS)
               {ret = ps3ntfs_stat(path, &fstat);stat.st_size = fstat.st_size;}
            else
                ret = sysLv2FsStat(path, &stat);

            if(ret < 0 || stat.st_size == 0) {ret = 0;goto skip2;}

            length = stat.st_size;
            if(flags & CPY_FILE1_IS_NTFS) {fd = ps3ntfs_open(path, O_RDONLY, 0);if(fd < 0) ret = FAILED; else ret = SUCCESS;}
            else
                ret = sysLv2FsOpen(path, 0, &fd, S_IRWXU | S_IRWXG | S_IRWXO, NULL, 0);
            if(ret) goto skip2;

            if(n == 0)
            {
                if(flags & CPY_FILE2_IS_NTFS)
                {
                    fd2 = ps3ntfs_open(path2, O_WRONLY | O_CREAT | O_TRUNC, 0);if(fd2 < 0) ret = FAILED; else ret = SUCCESS;
                    if(ret) goto skip2;
                }
                else
                {
                    ret = sysLv2FsOpen(path2, SYS_O_WRONLY | SYS_O_CREAT | SYS_O_TRUNC, &fd2, 0777, NULL, 0);
                    if(ret) goto skip2;
                    sysLv2FsChmod(path2, FS_S_IFMT | 0777);
                }
            }

            copy_parts = (length == 0) ? 0.0f : 100.0f / ((double) length / (double) 0x100000);
            copy_cpart = 0;

            ret = CopyFd(flags | CPY_NOTCLOSE, fd, fd2, mem, length);
            if(ret < 0) goto skip2;

            if(flags & CPY_FILE1_IS_NTFS) ps3ntfs_close(fd); else sysLv2FsClose(fd); fd = FAILED;
        }

        loop_wait0:

        if(use_async_fd)
        {
            if(!(my_f_async.flags & ASYNC_ENABLE))
            {
                if(flags & CPY_FILE2_IS_NTFS) ps3ntfs_close(fd2); else sysLv2FsClose(fd2);
                if(my_f_async.flags  & ASYNC_ERROR) {ret = 0x8001000C; goto skip2;}
            }
            else
                goto loop_wait0;
        }
    }
    else if(!strncmp(ext, ".666", 4))
    {
        // split files
        if(strcmp(ext, ".66600")) goto skip;

        int n;

        fd = fd2 = FAILED;

        mem = malloc(0x100000);
        if(!mem) {ret = (int) 0x80010004; goto skip2;}

        char *ext2 = get_extension(path2);

        if(!strncmp(ext2, ".666", 4)) ext2[0]=0;

        for(n = 0; n < 99; n++)
        {
            fd = FAILED; ext[4]= 48 + n/10; ext[5]= 48 + (n % 10);

            msgDialogProgressBarReset(MSG_PROGRESSBAR_INDEX1);
            msgDialogProgressBarSetMsg(MSG_PROGRESSBAR_INDEX1, dyn_get_name(path2));

            if(flags & CPY_FILE1_IS_NTFS)
               {ret = ps3ntfs_stat(path, &fstat);stat.st_size = fstat.st_size;}
            else
                ret = sysLv2FsStat(path, &stat);

            if(ret < 0 || stat.st_size == 0) {ret = 0;goto skip2;}

            length = stat.st_size;
            if(flags & CPY_FILE1_IS_NTFS)
            {
                fd = ps3ntfs_open(path, O_RDONLY, 0);
                if(fd < 0) ret = FAILED; else ret = SUCCESS;
            }
            else
                ret = sysLv2FsOpen(path, 0, &fd, S_IRWXU | S_IRWXG | S_IRWXO, NULL, 0);

            if(ret) goto skip2;

            if(n == 0)
            {
                if(flags & CPY_FILE2_IS_NTFS)
                {
                    fd2 = ps3ntfs_open(path2, O_WRONLY | O_CREAT | O_TRUNC, 0);if(fd2 < 0) ret = FAILED; else ret = SUCCESS;
                    if(ret) goto skip2;
                }
                else
                {
                    ret = sysLv2FsOpen(path2, SYS_O_WRONLY | SYS_O_CREAT | SYS_O_TRUNC, &fd2, 0777, NULL, 0);
                    if(ret) goto skip2;
                    sysLv2FsChmod(path2, FS_S_IFMT | 0777);
                }
            }

            copy_parts = (length == 0) ? 0.0f : 100.0f / ((double) length / (double) 0x100000);
            copy_cpart = 0;

            ret = CopyFd(flags | CPY_NOTCLOSE, fd, fd2, mem, length);
            if(ret < 0) goto skip2;

            if(flags & CPY_FILE1_IS_NTFS) ps3ntfs_close(fd); else sysLv2FsClose(fd); fd = FAILED;

        }

        loop_wait:

        if(use_async_fd) {

            if(!(my_f_async.flags & ASYNC_ENABLE))
            {
                if(flags & CPY_FILE2_IS_NTFS) ps3ntfs_close(fd2); else sysLv2FsClose(fd2);
                if(my_f_async.flags  & ASYNC_ERROR) {ret = 0x8001000C; goto skip2;}
            }
            else
                goto loop_wait;
        }

    }
    else
    {
        if(flags & CPY_FILE1_IS_NTFS)
        {
            ret = ps3ntfs_stat(path, &fstat);
            stat.st_size = fstat.st_size;
        }
        else
            ret = sysLv2FsStat(path, &stat);

        if(ret) goto skip;

        length = stat.st_size;

        if(length >= 0xFFFF0001LL &&
           strncmp(path2, "/dev_hdd0", 9) && is_ntfs_path(path2) == false)
        {
            // split the file
            if(flags & CPY_FILE1_IS_NTFS) {fd = ps3ntfs_open(path, O_RDONLY, 0);if(fd < 0) ret = FAILED; else ret = SUCCESS;}
            else
                ret = sysLv2FsOpen(path, 0, &fd, S_IRWXU | S_IRWXG | S_IRWXO, NULL, 0);
            if(ret) goto skip2;

            mem = malloc(0x100000);
            if(!mem) {ret = (int) 0x80010004; goto skip2;}

            u64 pos = 0;
            int n = 0;

            copy_parts = (length == 0) ? 0.0f : 100.0f / ((double) length / (double) 0x100000);
            copy_cpart = 0;

            char *ext2 =&path2[strlen(path2)];

            int is_iso = strlen(path2) > 4 && (!strcmp(ext2 - 4, ".iso") || !strcmp(ext2 - 4, ".ISO"));

            msgDialogProgressBarReset(MSG_PROGRESSBAR_INDEX1);

            while(pos < stat.st_size)
            {
                ext2[0] = 0;
                if(is_iso) sprintf(ext2,".%i", n);
                else sprintf(ext2,".666%2.2i", n);

                msgDialogProgressBarSetMsg(MSG_PROGRESSBAR_INDEX1, dyn_get_name(path2));

                length = (stat.st_size - pos);

                if(is_iso)
                {
                    if(length > 0xFFFF0000LL) length = 0xFFFF0000LL;
                }
                else
                {
                    if(length > 0x40000000LL) length = 0x40000000LL;
                }

                if(flags & CPY_FILE2_IS_NTFS) {fd2 = ps3ntfs_open(path2, O_WRONLY | O_CREAT | O_TRUNC, 0);if(fd2 < 0) ret = FAILED; else ret = SUCCESS;}
                else ret = sysLv2FsOpen(path2, SYS_O_WRONLY | SYS_O_CREAT | SYS_O_TRUNC, &fd2, 0777, NULL, 0);
                if(ret) goto skip2;

                if(!(flags & CPY_FILE2_IS_NTFS)) sysLv2FsChmod(path2, FS_S_IFMT | 0777);

                ret = CopyFd(flags, fd, fd2, mem, length);
                if(ret < 0) goto skip2;

                if(!use_async_fd)
                {
                    if(flags & CPY_FILE2_IS_NTFS) ps3ntfs_close(fd2); else sysLv2FsClose(fd2);
                }

                fd2 = FAILED;

                pos+= length;

                n++;
            }
        }
        else
        {
            if(flags & CPY_FILE1_IS_NTFS) {fd = ps3ntfs_open(path, O_RDONLY, 0);if(fd < 0) ret = FAILED; else ret = SUCCESS;}
            else ret = sysLv2FsOpen(path, 0, &fd, S_IRWXU | S_IRWXG | S_IRWXO, NULL, 0);
            if(ret) goto skip;


            if(flags & CPY_FILE2_IS_NTFS) {fd2 = ps3ntfs_open(path2, O_WRONLY | O_CREAT | O_TRUNC, 0);if(fd2 < 0) ret = FAILED; else ret = SUCCESS;}
            else ret = sysLv2FsOpen(path2, SYS_O_WRONLY | SYS_O_CREAT | SYS_O_TRUNC, &fd2, 0777, NULL, 0);

            if(ret) {if(flags & CPY_FILE1_IS_NTFS) ps3ntfs_close(fd); else sysLv2FsClose(fd); goto skip;}
            if(!(flags & CPY_FILE2_IS_NTFS)) sysLv2FsChmod(path2, FS_S_IFMT | 0777);


            mem = malloc(0x100000);
            if(!mem) {ret = (int) 0x80010004; goto skip2;}

            copy_parts = (length == 0) ? 0.0f : 100.0f / ((double) length / (double) 0x100000);
            copy_cpart = 0;

            ret = CopyFd(flags, fd, fd2, mem, length);
        }
    }


skip2:

    if(mem) free(mem);
    if(fd >= SUCCESS) {if(flags & CPY_FILE1_IS_NTFS) ps3ntfs_close(fd); else sysLv2FsClose(fd);}
    if(!use_async_fd) {if(fd2 >= SUCCESS){if(flags & CPY_FILE2_IS_NTFS) ps3ntfs_close(fd2); else sysLv2FsClose(fd2);}}
    if(ret > 0) ret = 0;

skip:

    if(progress_action == 2)
    {
        if(my_f_async.flags & ASYNC_ENABLE)
        {
            wait_event_thread();
            if(my_f_async.flags  & ASYNC_ERROR) {ret = 0x8001000C;}
        }

        unlink_secure(path2);
    }

    //msgDialogAbort();
    return ret;
}

int CopyDirectory(char* path, char* path2, char* path3)
{
    int dfd;
    u64 read;
    sysFSDirent dir;
    DIR_ITER *pdir = NULL;
    struct stat st;
    int ret = 0;
    int p1 = strlen(path);
    int p2 = strlen(path2);

    s32 flags = 0;

    // avoid recursive-infinite copy
    if(!strncmp(path, path3, strlen(path3))) return SUCCESS;

    if(is_ntfs_path(path )) flags|= CPY_FILE1_IS_NTFS;
    if(is_ntfs_path(path2)) flags|= CPY_FILE2_IS_NTFS;

    if(flags & CPY_FILE1_IS_NTFS)
    {
        pdir = ps3ntfs_diropen(path);
        if(pdir) ret = SUCCESS; else ret = FAILED;
    }
    else
        ret = sysLv2FsOpenDir(path, &dfd);

    if(ret) return FAILED;

    if(flags & CPY_FILE2_IS_NTFS) ps3ntfs_mkdir(path2, 0777); else sysLv2FsMkdir(path2, 0777);

    read = sizeof(sysFSDirent);

    while ((!(flags & CPY_FILE1_IS_NTFS) && !sysLv2FsReadDir(dfd, &dir, &read)) ||
           ( (flags & CPY_FILE1_IS_NTFS) && ps3ntfs_dirnext(pdir, dir.d_name, &st) == SUCCESS))
    {
        if (!(flags & CPY_FILE1_IS_NTFS) && !read)
            break;
        if (!strcmp(dir.d_name, ".") || !strcmp(dir.d_name, ".."))
            continue;

        if(flags & CPY_FILE1_IS_NTFS) {dir.d_type = (S_ISDIR(st.st_mode)) ? IS_DIRECTORY : IS_FILE;}

        path[p1]= 0;
        path2[p2]= 0;
        strcat(path, "/");
        strcat(path, dir.d_name);
        strcat(path2, "/");
        strcat(path2, dir.d_name);

        if (dir.d_type & IS_DIRECTORY)
        {
            // avoid recursive-infinite copy
            if(!strncmp(path, path3, strlen(path3))) {ret = 0;}
            else
            {
                ret = CopyDirectory(path, path2, path3);
                if(ret) goto skip;
            }
        }
        else
        {
            ret = CopyFile(path, path2);
            if(ret < 0) goto skip;
        }
    }

skip:

    path[p1] = 0;
    path2[p2] = 0;

    if(flags & CPY_FILE1_IS_NTFS) ps3ntfs_dirclose(pdir); else sysLv2FsCloseDir(dfd);

    return ret;
}

void pause_music(int pause);

static int copy_file_manager(char *path1, char *path2, sysFSDirent *ent, int nent, int sel, u64 free)
{
    int ret = 0;
    int n;

    u64 size = 0;

    //allow_shadow_copy = false;

    use_async_fd = ASYNC_ENABLE;
    pause_music(1);

    reset_copy = 1;
    cpy_str = "Copy";
    Files_To_Copy = 0;
    Folders_To_Copy = 0;

    int msg_en = 0;

    use_iso_splits = 0;
    if(!strncmp(path2, "/dev_hdd0", 9))
    {
        use_iso_splits = 1;
        if(allow_shadow_copy && !strncmp(path1, "/dev_hdd0", 9)) cpy_str = "Shadow Copy";
    }


    if(sel >= 0)
    {
        sprintf(MEM_MESSAGE, "Do you want to %s %s\n\nfrom %s\n\nto %s?", cpy_str, ent[sel].d_name, path1, path2);

        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
        {
            double_bar(cpy_str);
            msg_en = 1;

            sprintf(TEMP_PATH1 , "%s/%s", path1, ent[sel].d_name);
            sprintf(TEMP_PATH2 , "%s/%s", path2, ent[sel].d_name);
            sprintf(TEMP_PATH  , "%s/%s", path2, ent[sel].d_name);

            if(ent[sel].d_type & IS_DIRECTORY)
            {
                ret = CountFiles(TEMP_PATH1, &Files_To_Copy, &Folders_To_Copy, &size);

                if(ret < 0) goto end;
                if(allow_shadow_copy == false && size > free) goto end;

                sprintf(TEMP_PATH1, "%s/%s", path1, ent[sel].d_name);
                ret = CopyDirectory(TEMP_PATH1, TEMP_PATH2, TEMP_PATH);
            }
            else
            {
                if(is_ntfs_path(TEMP_PATH1))
                {
                    struct stat fstat;
                    ret = ps3ntfs_stat(TEMP_PATH1, &fstat);
                    size+= fstat.st_size;
                }
                else
                {
                    sysFSStat stat;
                    ret = sysLv2FsStat(TEMP_PATH1, &stat);
                    size+= stat.st_size;
                }

                if(ret != SUCCESS) goto end;
                if(allow_shadow_copy == false && size > free) goto end;

                Files_To_Copy = 1;

                ret = CopyFile(TEMP_PATH1, TEMP_PATH2);
            }

            msgDialogAbort();
            usleep(100000);
            msg_en = 0;
        }
    }
    else
    {
        // multiple
        sprintf(MEM_MESSAGE, "Do you want to %s the selected Files and Folders\n\nfrom %s\n\nto %s?", cpy_str, path1, path2);

        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
        {
            double_bar(cpy_str);
            msg_en = 1;

            for(n = 0; n < nent; n++)
            {
                if(!(ent[n].d_type & IS_MARKED)) continue; // skip no marked

                sprintf(TEMP_PATH, "%s/%s", path1, ent[n].d_name);

                if(ent[n].d_type & IS_DIRECTORY) ret = CountFiles(TEMP_PATH, &Files_To_Copy, &Folders_To_Copy, &size);
                else
                {
                    if(is_ntfs_path(TEMP_PATH))
                    {
                        struct stat fstat;
                        ret = ps3ntfs_stat(TEMP_PATH, &fstat);
                        size+= fstat.st_size;
                    }
                    else
                    {
                        sysFSStat stat;
                        ret = sysLv2FsStat(TEMP_PATH, &stat);
                        size+= stat.st_size;
                    }

                    Files_To_Copy++;
                }

                if(ret < 0) goto end;
                if(allow_shadow_copy == false && size > free) goto end;
            }

            if(ret == 0)
            for(n = 0; n < nent; n++)
            {
                if(!(ent[n].d_type & IS_MARKED)) continue; // skip no marked

                sprintf(TEMP_PATH1, "%s/%s", path1, ent[n].d_name);
                sprintf(TEMP_PATH2, "%s/%s", path2, ent[n].d_name);
                sprintf(TEMP_PATH , "%s/%s", path2, ent[n].d_name);

                if(ent[n].d_type & IS_DIRECTORY)
                    ret = CopyDirectory(TEMP_PATH1, TEMP_PATH2, TEMP_PATH);
                else
                    ret = CopyFile(TEMP_PATH1, TEMP_PATH2);

                if(ret <0) break;
            }
        }

        msgDialogAbort();
        usleep(100000);
        msg_en = 0;
    }

 end:

    use_iso_splits = 0;

    if(msg_en)
    {
        msgDialogAbort();
        usleep(100000);
    }

    if(use_async_fd)
    {
        if(my_f_async.flags & ASYNC_ENABLE)
        {
            wait_event_thread();
            if(my_f_async.flags  & ASYNC_ERROR) {ret = 0x8001000C;}
        }

        event_thread_send(0x555ULL, (u64) 0, 0);
    }

    use_async_fd = 0;
    pad_last_time = 0;

    pause_music(0);

    if(ret < 0) ;
    else if(allow_shadow_copy == false && size > free)
    {
        DrawDialogOK("There is not enough free space to Copy Files/Folders");
    }

    allow_shadow_copy = true;
    return ret;
}

int copy_archive_file(char *path1, char *path2, char *file, u64 free)
{
    int ret = 0;
    u64 size = 0;
    int n, len;
    int nfiles = 0;
    int multi = 0;
    struct stat s;
    int msg_en = 0;

    use_async_fd = ASYNC_ENABLE;
    pause_music(1);

    reset_copy = 1;
    cpy_str = "Copy";

    Files_To_Copy = 0;
    Folders_To_Copy = 0;

    use_iso_splits = 0;
    if(!strncmp(path2, "/dev_hdd0", 9)) use_iso_splits = 1;

    len = strlen(file);
    if(len > 6 && strcasecmp(file + len - 6, ".iso.0") == SUCCESS) {

        file[len - 2] = 0;
        multi = 1;

        for(n = 0; n < 64; n++)
        {
            sprintf(TEMP_PATH, "%s/%s.%i", path1, file, n);
            if(stat(TEMP_PATH, &s) == SUCCESS)
            {
                Files_To_Copy++;
                nfiles++;
                size += s.st_size;
            }
            else
                break;
        }

        if(use_iso_splits)
        {
            multi = 0;
            Files_To_Copy = 1;
            nfiles = 1;
            file[len - 2] = '.';
        }
    }
    else
    {
        Files_To_Copy = 1;
        nfiles = 1;

        sprintf(TEMP_PATH, "%s/%s", path1, file);
        if(stat(TEMP_PATH, &s) == SUCCESS)
        {
            size += s.st_size;
        }
    }


    sprintf(MEM_MESSAGE, "Copy %s\n\nfrom %s\n\nto %s?", file, path1, path2);
    if(DrawDialogYesNo(MEM_MESSAGE) == YES)
    {
        double_bar(cpy_str);
        msg_en = 1;

        if(size > free || size == 0) goto end;

        for(n = 0; n < nfiles; n++)
        {
            if(multi)
            {
                sprintf(TEMP_PATH1, "%s/%s.%i", path1, file, n);
                sprintf(TEMP_PATH2, "%s/%s.%i", path2, file, n);

            }
            else
            {
                sprintf(TEMP_PATH1, "%s/%s", path1, file);
                sprintf(TEMP_PATH2, "%s/%s", path2, file);
            }


            ret = CopyFile(TEMP_PATH1, TEMP_PATH2);
            if(ret < 0) goto end;
        }

        msgDialogAbort();
        usleep(100000);
        msg_en = 0;
    }


 end:

    use_iso_splits = 0;

    if(msg_en)
    {
        msgDialogAbort();
        usleep(100000);
    }

    if(use_async_fd)
    {
        if(my_f_async.flags & ASYNC_ENABLE)
        {
            wait_event_thread();
            if(my_f_async.flags  & ASYNC_ERROR) {ret = 0x8001000C;}
        }

        event_thread_send(0x555ULL, (u64) 0, 0);
    }

    use_async_fd = 0;
    pad_last_time = 0;

    pause_music(0);

    if(ret < 0)
    {
        sprintf(MEM_MESSAGE, "Copy error: 0x%08x\n\n%s", ret, getlv2error(ret));
        DrawDialogOK(MEM_MESSAGE);
        return ret;
    }

    if(size > free)
    {
        DrawDialogOK("There is not free space to Copy the Files/Folders");
    }

    return ret;
}

static int move_file_manager(char *path1, char *path2, sysFSDirent *ent, int nent, int sel, u64 free)
{
    int ret = 0;
    int n;
    int flag = 0;

    u64 size = 0;

    use_async_fd = ASYNC_ENABLE;

    pause_music(1);

    n = 1; while(path1[n] != '/' && path1[n] != 0) n++;

    if(!strncmp(path1, path2, n - 1)) flag = 1; // can move

    cpy_str = "Move";
    Files_To_Copy = 0;
    Folders_To_Copy = 0;

    reset_copy = 1;


    if(sel >= 0)
    {
        sprintf(MEM_MESSAGE, "Do you want to Move %s\n\nfrom %s\n\nto %s?", ent[sel].d_name, path1, path2);
        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
        {
            double_bar(cpy_str);

            sprintf(TEMP_PATH1, "%s/%s", path1, ent[sel].d_name);
            sprintf(TEMP_PATH2, "%s/%s", path2, ent[sel].d_name);
            sprintf(TEMP_PATH , "%s/%s", path2, ent[sel].d_name);

            if(flag)
            {
                ret = rename_secure(TEMP_PATH1, TEMP_PATH2);
            }
            else if(ent[sel].d_type & IS_DIRECTORY)
            {
                ret = CountFiles(TEMP_PATH1, &Files_To_Copy, &Folders_To_Copy, &size);

                if(ret < 0) goto end;
                if(size > free) goto end;

                sprintf(TEMP_PATH1, "%s/%s", path1, ent[sel].d_name);
                ret = CopyDirectory(TEMP_PATH1, TEMP_PATH2, TEMP_PATH);

                if(ret == 0)
                {
                    DeleteDirectory(TEMP_PATH1);
                    if(is_ntfs_path(TEMP_PATH1))
                        ret = ps3ntfs_unlink(TEMP_PATH1);
                    else
                        ret = rmdir_secure(TEMP_PATH1);
                }
            }
            else
            {
                if(is_ntfs_path(TEMP_PATH1))
                {
                    struct stat fstat;
                    ret = ps3ntfs_stat(TEMP_PATH1, &fstat);
                    size+= fstat.st_size;
                }
                else
                {
                    sysFSStat stat;
                    ret = sysLv2FsStat(TEMP_PATH1, &stat);
                    size+= stat.st_size;
                }

                if(ret != SUCCESS) goto end;
                if(size > free) goto end;

                Files_To_Copy = 1;
                ret = CopyFile(TEMP_PATH1, TEMP_PATH2);

                if(ret == 0) ret = unlink_secure(TEMP_PATH1);
            }

            msgDialogAbort();
            usleep(100000);
        }
    }
    else
    {
        // multiple
        sprintf(MEM_MESSAGE, "Do you want to Move the selected Files and Folders\n\nfrom %s\n\nto %s?", path1, path2);
        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
        {
            double_bar(cpy_str);

            if(!flag)
            for(n = 0; n < nent; n++)
            {
                if(!(ent[n].d_type & IS_MARKED)) continue; // skip no marked

                sprintf(TEMP_PATH1, "%s/%s", path1, ent[n].d_name);


                if(ent[n].d_type & IS_DIRECTORY) ret = CountFiles(TEMP_PATH1, &Files_To_Copy, &Folders_To_Copy, &size);
                else
                {
                    if(is_ntfs_path(TEMP_PATH1))
                    {
                        struct stat fstat;
                        ret = ps3ntfs_stat(TEMP_PATH1, &fstat);
                        size+= fstat.st_size;
                    }
                    else
                    {
                        sysFSStat stat;
                        ret = sysLv2FsStat(TEMP_PATH1, &stat);
                        size+= stat.st_size;
                    }

                    Files_To_Copy++;
                }

                if(ret < 0) goto end;
                if(size > free) goto end;
            }

            if(ret == 0)
            for(n = 0; n < nent; n++)
            {
                if(!(ent[n].d_type & IS_MARKED)) continue; // skip no marked

                sprintf(TEMP_PATH1, "%s/%s", path1, ent[n].d_name);
                sprintf(TEMP_PATH2, "%s/%s", path2, ent[n].d_name);

                if(flag)
                {
                    ret = rename_secure(TEMP_PATH1, TEMP_PATH2);
                }
                else if(ent[n].d_type & IS_DIRECTORY)
                {
                    sprintf(TEMP_PATH , "%s/%s", path2, ent[n].d_name);
                    ret = CopyDirectory(TEMP_PATH1, TEMP_PATH2, TEMP_PATH);
                    if(ret == 0)
                    {
                        DeleteDirectory(TEMP_PATH1);
                        if(is_ntfs_path(TEMP_PATH1))
                            ret = ps3ntfs_unlink(TEMP_PATH1);
                        else
                            ret = rmdir_secure(TEMP_PATH1);
                    }
                }
                else
                {
                    ret = CopyFile(TEMP_PATH1, TEMP_PATH2);
                    if(ret == 0)
                    {
                        if(is_ntfs_path(TEMP_PATH1))
                            ret = ps3ntfs_unlink(TEMP_PATH1);
                        else
                            ret = unlink_secure(TEMP_PATH1);
                    }
                }

                if(ret < 0) break;
            }
            msgDialogAbort();
            usleep(100000);
        }
    }

 end:
     if(use_async_fd)
     {
        if(my_f_async.flags & ASYNC_ENABLE)
        {
            wait_event_thread();
            if(my_f_async.flags  & ASYNC_ERROR) {ret = 0x8001000C;}
        }

        event_thread_send(0x555ULL, (u64) 0, 0);
    }

    use_async_fd = 0;
    pad_last_time = 0;

    pause_music(0);

    if(ret < 0) return ret;

    if(size > free)
    {
        msgDialogAbort();
        usleep(100000);
        DrawDialogOK("There is not free space to Move Files/Folders");
    }

    return ret;
}

#undef AUTO_BUTTON_REP2
#define AUTO_BUTTON_REP2(v, b) if(v && (old_pad & b)) { \
                                 v++; \
                                 if(v > 10) {v = 0; new_pad |= b;} \
                               } else v = 0;

#ifndef LOADER_MODE
static void display_icon(int x, int y, int z, int icon)
{
    tiny3d_SetTextureWrap(0, Png_res_offset[7 + icon], Png_res[7 + icon].width,
                          Png_res[7 + icon].height, Png_res[7 + icon].wpitch,
                          TINY3D_TEX_FORMAT_A8R8G8B8,  TEXTWRAP_CLAMP, TEXTWRAP_CLAMP,1);

    DrawTextBox(x+2, y, z, 18, 18, WHITE);
}


#define FD_LV1 -1
#define FD_LV2 -2

static u64 begin_lv1 = 0x0;
static u64 begin_lv2 = 0x0;
static u64 size_lv1 = 0x10000000ULL;
static u64 size_lv2 = 0x800000ULL;


int read_LV1(u64 pos, char *mem, int size)
{
    int n = 0;
    u64 temp;

    lv1_reg regs_i, regs_o;

    if(begin_lv1 > pos) return (int) 0x8001002B;

    if(pos + ((u64) size) > size_lv1)  size -= (int) (pos + ((u64) size) - size_lv1);

    if(firmware < 0x421C) return (int) 0x80010009;

    temp = pos;

    if(temp & 7)
    {
        n= 8 - (pos & 7);
        if(n > size) n = size;
        temp&= ~7ULL;
        regs_i.reg3 = temp;
        regs_i.reg11 = 0xB6;
        sys8_lv1_syscall(&regs_i, &regs_o);
        memcpy(&mem[0], ((char *) &regs_o.reg4) + (pos & 7), n);

        temp += 8;
    }

    if(n < size)
    {
        for(; n < size; n += 8)
        {
            regs_i.reg3 = temp;
            regs_i.reg11 = 0xB6;
            sys8_lv1_syscall(&regs_i, &regs_o);
            memcpy(&mem[n], ((char *) &regs_o.reg4), ((n+8) > size) ? (size - n) : 8);
            temp += 8;
        }
    }

    return SUCCESS;
}

int read_LV2(u64 pos, char *mem, int size)
{
    int n = 0;
    u64 temp;
    u64 temp2;

    if(begin_lv2 > pos) return (int) 0x8001002B;

    if(pos + ((u64) size) > size_lv2)  size -= (int) (pos + ((u64) size) - size_lv2);

    temp = pos;

    if(temp & 7)
    {
        n= 8 - (pos & 7);
        if(n > size) n = size;
        temp&= ~7ULL;
        temp2 = lv2peek(0x8000000000000000ULL + temp);

        memcpy(&mem[0], ((char *) &temp2) + (pos & 7), n);

        temp += 8;
    }

    if(n < size)
    {
        for(; n < size; n += 8)
        {
            temp2 = lv2peek(0x8000000000000000ULL + temp);
            memcpy(&mem[n], ((char *) &temp2), ((n+8) > size) ? (size - n) : 8);
            temp += 8;
        }
    }

    return SUCCESS;
}

int write_LV1(u64 pos, char *mem, int size)
{
    int n = 0;
    u64 temp;

    lv1_reg regs_i, regs_o;

    if(begin_lv1 > pos) return (int) 0x8001002B;

    if(pos + ((u64) size) > size_lv1)  size -= (int) (pos + ((u64) size) - size_lv1);

    if(firmware < 0x421C) return (int) 0x80010009;

    temp = pos;

    if(temp & 7)
    {
        n= 8 - (pos & 7);
        if(n > size) n = size;
        temp&= ~7ULL;
        regs_i.reg3 = temp;
        regs_i.reg11 = 0xB6;
        sys8_lv1_syscall(&regs_i, &regs_o);
        memcpy(((char *) &regs_o.reg4) + (pos & 7), &mem[0], n);

        regs_i.reg4 = regs_o.reg4;
        regs_i.reg11 = 0xB7;
        sys8_lv1_syscall(&regs_i, &regs_o);

        temp += 8;
    }

    if(n < size)
    {
        for(; n < size; n += 8)
        {
            regs_i.reg3 = temp;
            regs_i.reg11 = 0xB6;
            sys8_lv1_syscall(&regs_i, &regs_o);
            memcpy(((char *) &regs_o.reg4), &mem[n], ((n+8) > size) ? (size - n) : 8);
            regs_i.reg4 = regs_o.reg4;
            regs_i.reg11 = 0xB7;
            sys8_lv1_syscall(&regs_i, &regs_o);
            temp += 8;
        }
    }

    return SUCCESS;
}

int write_LV2(u64 pos, char *mem, int size)
{
    int n = 0;
    u64 temp;
    u64 temp2;

    temp = pos;

    if(begin_lv2 > pos) return (int) 0x8001002B;

    if(pos + ((u64) size) > size_lv2)  size -= (int) (pos + ((u64) size) - size_lv2);

    if(temp & 7)
    {
        n= 8 - (pos & 7);
        if(n > size) n = size;
        temp &= ~7ULL;

        temp2 = lv2peek(0x8000000000000000ULL + temp);
        memcpy(((char *) &temp2) + (pos & 7), &mem[0], n);
        lv2poke(0x8000000000000000ULL + temp, temp2);

        temp += 8;
    }

    if(n < size)
    {
        for(; n < size; n += 8)
        {
            temp2 = lv2peek(0x8000000000000000ULL + temp);
            memcpy(((char *) &temp2), &mem[n], ((n+8) > size) ? (size - n) : 8);
            lv2poke(0x8000000000000000ULL + temp, temp2);
            temp += 8;
        }
    }

    return SUCCESS;
}

static int load_hex(bool is_ntfs, s32 fd, u64 pos, void *buffer, u64 readed)
{
    int ret;
    u64 temp = 0;

    if(fd == FD_LV1)
    {
        ret = read_LV1(pos, buffer, (int) readed);

        if(ret != 0)
        {
            sprintf(MEM_MESSAGE, "Read Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
        }

        return ret;
    }
    else if(fd == FD_LV2)
    {

        ret = read_LV2(pos, buffer, (int) readed);

        if(ret != 0)
        {
            sprintf(MEM_MESSAGE, "Read Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
        }

        return ret;
    }

    if(is_ntfs)
    {
        temp = ps3ntfs_seek64(fd, pos, 0);
        if(temp < 0) ret = FAILED; else ret = SUCCESS;
    }
    else
        ret = sysLv2FsLSeek64(fd, pos, 0, &temp);

    if(ret < 0 || pos != temp)
    {
        if(ret == 0) ret = (int) 0x8001001E;
        sprintf(MEM_MESSAGE, "Lseek Error: 0x%08x\n\n%s", ret, getlv2error(ret));
        DrawDialogOK(MEM_MESSAGE);

    }
    else
    {
        temp = 0;
        if(is_ntfs)
        {
            ret = ps3ntfs_read(fd, buffer, readed);
            temp = (u64) ret; if(ret > 0) ret = 0;
        }
        else
            ret = sysLv2FsRead(fd, buffer, readed, &temp);

        if(ret < 0 || readed != temp)
        {
            if(ret == 0) ret = (int) 0x8001002B;
            sprintf(MEM_MESSAGE, "Read Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
        }
    }

    return ret;
}

static int save_hex(bool is_ntfs, s32 fd, u64 pos, void *buffer, u64 readed)
{
    int ret;
    u64 temp = 0;

    if(fd == FD_LV1)
    {
        ret = write_LV1(pos, buffer, (int) readed);

        if(ret != 0)
        {
            sprintf(MEM_MESSAGE, "Write Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
        }

        return ret;
    }
    else if(fd == FD_LV2)
    {
        ret = write_LV2(pos, buffer, (int) readed);

        if(ret != 0)
        {
            sprintf(MEM_MESSAGE, "Write Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
        }

        return ret;
    }

    if(is_ntfs)
    {
        temp = ps3ntfs_seek64(fd, pos, 0);
        if(temp < 0) ret = FAILED; else ret = SUCCESS;
    }
    else
        ret = sysLv2FsLSeek64(fd, pos, 0, &temp);

    if(ret < 0 || pos != temp) {
        if(ret == 0) ret = (int) 0x8001001E;
        sprintf(MEM_MESSAGE, "Lseek Error: 0x%08x\n\n%s", ret, getlv2error(ret));
        DrawDialogOK(MEM_MESSAGE);

    }
    else
    {
        temp = 0;
        if(is_ntfs)
        {
            ret = ps3ntfs_write(fd, buffer, readed);
            temp = (u64) ret; if(ret>0) ret = 0;
        }
        else
            ret = sysLv2FsWrite(fd, buffer, readed, &temp);

        if(ret < 0 || readed != temp)
        {
            if(ret == 0) ret = (int) 0x8001002B;
            sprintf(MEM_MESSAGE, "Write Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
        }
    }

    return ret;
}

int memcmp_case(char * p1, char *p2, int len)
{
    int n;
    char a, b;

    for(n = 0; n < len; n++)
    {
        a = *p1++; b = *p2++;
        if(a >= 'A' && a <= 'Z') a += 32;
        if(b >= 'A' && b <= 'Z') b += 32;
        if(a != b) return FAILED;
    }

    return SUCCESS;
}

static int find_mode = FIND_HEX_MODE;

static int find_in_file(bool is_ntfs, s32 fd, u64 pos, u64 size, u64 *found, void * str, int len, int s)
{

    u64 temp;
    u64 readed = 0;
    u32 n;
    int ret = 0;
    int flag = 2;
    u64 pos0 = pos;

    *found = TEXTNOTFOUND;

    char *mem =  malloc(0x8208);
    if(!mem) return (int) 0x80010004;
    memset(mem, 0, 0x8200);

    single_bar("finding in file...");

    float parts;

    if(s < 0) parts = 100.0f / ((double) pos / (double) 0x8000);
    else parts = 100.0f / ((double) (size - pos) / (double) 0x8000);

    float cpart = (s >= 0) ? parts * ((double) pos / (double) 0x8000) : 0;

    while((s >= 0 && pos < size) || (s < 0 && pos >= 0 && flag))
    {
        if(fd == FD_LV1 || fd == FD_LV2)
        {
            ret = 0;
            if(fd == FD_LV1) {if(begin_lv1 > pos) ret =(int) 0x8001001E; if(pos >= size_lv1) temp = 0; else  temp = pos;}
            if(fd == FD_LV2) {if(begin_lv2 > pos) ret =(int) 0x8001001E; if(pos >= size_lv2) temp = 0; else  temp = pos;}
        }
        else
        {
            if(is_ntfs)
                {temp = ps3ntfs_seek64(fd, pos, 0); if(temp < 0) ret = FAILED; else ret = SUCCESS;}
            else
                ret = sysLv2FsLSeek64(fd, pos, 0, &temp);
        }

        if(ret < 0 || pos != temp)
        {
            if(ret == 0) ret = (int) 0x8001001E;
            msgDialogAbort();
            sprintf(MEM_MESSAGE, "Lseek Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
            goto skip;

        }

        readed = size - pos; if(readed > 0x8200ULL) readed = 0x8200ULL;

        if(fd == FD_LV1)
        {
            ret = read_LV1(pos, mem, (int) readed);
            temp = readed;
        }
        else if(fd == FD_LV2)
        {
            ret = read_LV2(pos, mem, (int) readed);
            temp = readed;
        }
        else
        {
            if(is_ntfs)
            {
                ret = ps3ntfs_read(fd, mem, readed);
                temp = (u64) ret; if(ret > 0) ret = 0;
            }
            else
                ret =sysLv2FsRead(fd, mem, readed, &temp);
        }

        if(ret < 0 || readed != temp)
        {
            if(ret == 0) ret = 0x8001000C;
            msgDialogAbort();
            sprintf(MEM_MESSAGE, "Read Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);

            goto skip;
        }

        readed-= 0x200ULL * (readed == 0x8200ULL); // resta area solapada de busqueda

        for(n = 0; n < (u32) readed; n++)
        {
            if(find_mode == FIND_CASE_INSENSITIVE_MODE)
            {
                if(((pos + (u64) n) < pos0 || s >= 0) && !memcmp_case(mem + n, str, len))
                {
                    *found = pos + (u64) n;
                    goto skip;
                }
            }
            else if(((pos + (u64) n) < pos0 || s >= 0) && !memcmp(mem + n, str, len))
            {
                *found = pos + (u64) n;
                goto skip;
            }
        }

        if(s >= 0)
        {
            pos += readed;
        }
        else
        {
            if(pos < readed) {pos = 0ULL; flag--;} else  pos -= readed;
        }

        if(progress_action == 2) {ret = 0x8001000C; goto skip;}

        cpart += parts;
        if(cpart >= 1.0f)
        {
            update_bar((u32) cpart);
            cpart-= (float) ((u32) cpart);
        }
    }

skip:
    if(mem) free(mem);
    msgDialogAbort();

    return ret;
}

static char help2[] = {
    "HELP - [ Hex Editor]\n"
    "\n"
    "CROSS   - Select the option\n"
    "UP/DOWN - Select option\n"
    "\n"
    "START   - Open/Close this menu\n"
    "CIRCLE  - Exit\n"
};

static char help3[] = {
    "SELECT   - Show help window\n"
    "CROSS    - Increase the selected nibble\n"
    "TRIANGLE - Decrease the selected nibble\n"
    "L2/R2    - Decrease/increase the selected byte (pressing to auto-repeat)\n"
    "\n"
    "SQUARE   - Mark Area / Undo the changes in selected byte \n"
    "SELECT + SQUARE - Undo the current windows changes\n"
    "\n"
    "START    - Opens menu selector (go to, find..)\n"
    "CIRCLE   - Exit from Hex Editor\n"
    "\n"
    "UP/DOWN/LEFT/RIGHT - Move the cursor\n"
    "\n"
    "L1/R1 - Move back/forward from the file\n"
    "L3/R3 - Find back/forward\n"
    "\n"
    "Special Note: Changes in the window must be saved to use some actions with implicit changes"
    "in the editor window. Pressing CIRCLE you can save or discard the window changes.\n"
};

static char help4[] = {
    "SELECT   - Show this help window\n"
    "\n"
    "CROSS    - Set the hex number\n"
    "SQUARE   - Delete the last digit\n"
    "\n"
    "UP/DOWN/LEFT/RIGHT - Move the cursor to the keyboard\n"
    "L2/R2    - Move back/forward from the number window\n"
    "\n"
    "START    - Go to the Address\n"
    "\n"
    "CIRCLE   - Close the window\n"
    "\n"
    "Special Note: jump to the absolute file address"
};

static char help5[] = {
    "SELECT   - Show this help window\n"
    "\n"
    "CROSS    - Set the hex number\n"
    "SQUARE   - Delete the last digit\n"
    "\n"
    "UP/DOWN/LEFT/RIGHT - Move the cursor to the keyboard\n"
    "L2/R2    - Move back/forward from the number window\n"
    "L1/R1    - Decrease/increase the number of bytes to find\n"
    "\n"
    "START    - Find Hex values in file (forward)\n"
    "\n"
    "START (pressing) - Open/close this help window\n"
    "\n"
    "CIRCLE   - Close the window\n"
    "\n"
    "Special Note: Find Hex values in the file. You can use L3/R3 from    "
    "the Hex Editor window to find the previous/next result from the     current file position\n"
};
#endif

enum hex_modes
{
    HEX_EDIT_FILE = 0,
    HEX_EDIT_RAM  = 1,
    HEX_EDIT_LV2  = 2,
};

static int mark_flag = 0;
static u64 mark_ini = 0ULL;
static u32 mark_len = 0x0;

static void *copy_mem = NULL;
static u32 copy_len = 0;

static u64 lv1_pos = 0ULL;
static u64 lv2_pos = 0ULL;


#ifdef LOADER_MODE
void draw_hex_editor() {}
void hex_editor(int hex_mode, char *path, s64 size) {}
#else
void draw_hex_editor()
{
    int n, m;

    int px = 0, py = 0;
    frame++; if(frame > 300) frame = 0;

    tiny3d_Flip();
    ps3pad_read();

    tiny3d_Project2D();
    cls2();
    update_twat(false);

    DrawBox(0, 0, 0, 848, 32, BLUE5);
    DrawBox2(0, 32, 0, 848, 448);

    DrawBox(0, 480, 0, 848, 32, BLUE5);


    SetFontColor(WHITE, 0x0);

    SetCurrentFont(FONT_BUTTON);

    SetFontSize(8, 16);

    py = 40;

    #define START_X 80

    px = START_X;  DrawString(px, py, "      Offset ");
    px = START_X + 16 + 17 *8 + 4;

    for(m = 0; m < 16; m++)
    {
        if(m == 8) px += 8;
        DrawFormatString(px, py,  "%2X", m);
        px += 24;
    }

    py += 24;

    // 0x180
    for(n = 0; n < 24; n++)
    {
       px = START_X;
       u32 color = WHITE;

       SetFontSize(8, 16);
       SetFontColor(color, 0x0);

       // draw hex
       px = DrawFormatString(px, py, " %08X", (u32) (((pos + (u64) (n<<4)))>>32));
       px = DrawFormatString(px, py,  "%08X", (u32)   (pos + (u64) (n<<4))); px+= 16;

       // draw hex
       for(m = 0; m < 16; m++)
       {
           int sel = 0;
           if(m == 8) px += 8;
           px += 8;

           sel = mark_flag == 2 && (pos + (u64) ((n<<4) + m)) >= mark_ini && (pos + (u64) ((n<<4) + m)) < (mark_ini + (u64) mark_len);

           if(temp_buffer[HEX_EDIT + (n<<4) + m] == temp_buffer[HEX_READ + (n<<4) + m])
               color = WHITE;
           else
               color = GREEN;

           // first nibble
           if(((n<<4) + m) >= readed) color = GRAY;

           if((e_x) == (m<<1) && e_y == n)
           {
               if(frame & BLINK)
                   SetFontColor(color, (sel) ? CYAN2 : ((color == GREEN) ? BLUE5 : MAGENTA));
               else
                   SetFontColor(BLACK, color);
           }
           else
               SetFontColor(color, (sel) ? CYAN2 : ((color == GREEN) ? BLUE5 : INVISIBLE));

           px = DrawFormatString(px, py, "%X", (temp_buffer[HEX_EDIT + (n<<4) + m])>>4);

           // second nibble
           if(((n<<4) + m) >= readed) color = GRAY;

           if((e_x) == (m<<1)+1 && e_y == n)
           {
              if(frame & BLINK)
                  SetFontColor(color, (sel) ? CYAN2 : ((color == GREEN) ? BLUE5 : MAGENTA));
              else
                  SetFontColor(BLACK, color);
           }
           else   SetFontColor(color, (sel) ? CYAN2 : ((color == GREEN) ? BLUE5 : INVISIBLE));

           px = DrawFormatString(px, py, "%X", temp_buffer[HEX_EDIT + (n<<4) + m] & 0xF);
       }

       px += 16;

       SetFontColor(WHITE, INVISIBLE);

       // draw chars
       for(m = 0; m < 16; m++)
       {
            u8 ch = temp_buffer[HEX_EDIT + (n<<4) + m];
            int sel = 0;

            sel = mark_flag == 2 && (pos + (u64) ((n<<4) + m)) >= mark_ini && (pos + (u64) ((n<<4) + m)) < (mark_ini + (u64) mark_len);

            if(temp_buffer[HEX_EDIT + (n<<4) + m] == temp_buffer[HEX_READ + (n<<4) + m]) color = WHITE;
            else color = GREEN;

            if(((n<<4) + m) >= readed) color = GRAY;

            if((e_x>>1) == m && e_y == n)
            {
                if(frame & BLINK)
                    SetFontColor(color, (sel) ? CYAN2 : ((color == GREEN) ? BLUE5 : MAGENTA));
                else
                    SetFontColor(BLACK, color);
            }
            else    SetFontColor(color, (sel) ? CYAN2 : ((color == GREEN) ? BLUE5 : INVISIBLE));


            px = DrawFormatString(px, py, "%c", ch == 0 ? '.' : (ch < 32 ? '?' : (char) ch));
       }

       py += 16;
    }

    py += 2;
    SetFontColor(WHITE, INVISIBLE);
    SetFontAutoCenter(1);

    SetFontSize(8, 16);
    DrawFormatString(px, py, "Size: %08X%08X (%1.0f)", (u32) (hex_filesize>>32), (u32) (hex_filesize), (double) (hex_filesize));
    DrawFormatString(px, py + 14, "File at %1.4f%%", 100.0f * (double) (pos + (u64) ((e_y * 0x10) + (e_x>>1))) / (double) hex_filesize);
    SetFontAutoCenter(0);


    set_ttf_window(8, 0, 752, 32, WIN_AUTO_LF);
    display_ttf_string(0, 0, (char *) hex_path, GREEN, 0, 12, 20);
}

void hex_editor(int hex_mode, char *path, s64 size)
{
    int n, m;
    int px, py;

    int help = 0;

    s32 fd = FAILED;
    u64 temp;

    bool read_only = false;

    pos = 0;
    readed = 0;
    e_x = 0, e_y = 0;

    int ret;

    bool modified = false;

    enum function_menu_options
    {
        HEX_EDIT_MODE    = 0,
        HEX_GOTO_ADDRESS = 1,
        HEX_FIND_VALUE   = 2,
    };

    int function_menu = HEX_EDIT_MODE;
    int enable_menu = 0;
    int start_status = 0;

    int auto_up = 0, auto_down = 0;
    int auto_left = 0, auto_right = 0;
    int auto_l2 = 0, auto_r2 = 0;
    int auto_l1 = 0, auto_r1 = 0;
    int auto_l11 = 0, auto_r11 = 0;

    int f_key = 0;
    int f_pos = 0;
    int f_len = 8;
    static u8 find[512];
    int find_len = 4;

    bool is_ntfs = false;

    mark_flag = 0;
    mark_ini = 0ULL;
    mark_len = 0x0;

    memset((char *) find, 0, 512);

    if(hex_mode == HEX_EDIT_FILE)
    {
        is_ntfs = is_ntfs_path(path);

        hex_filesize = size;

        if(hex_filesize == 0ULL) return; // ignore zero files

        if(!is_ntfs)
        {
            ret = sysLv2FsOpen(path, SYS_O_RDWR, &fd, S_IRWXU | S_IRWXG | S_IRWXO, NULL, 0);
            if(ret != SUCCESS)
            {
                read_only = true;
                ret = sysLv2FsOpen(path, 0, &fd, S_IRWXU | S_IRWXG | S_IRWXO, NULL, 0);
            }
        }
        else
        {
            fd = ps3ntfs_open(path, O_RDWR, 0);
            if(fd < 0)
            {
                read_only = true;
                fd = ps3ntfs_open(path, O_RDONLY, 0);
            }
            if(fd < 0) ret = FAILED; else ret = SUCCESS;
        }

        if(ret != SUCCESS) {sprintf(MEM_MESSAGE, "Error: Cannot read %s", path); DrawDialogOK(MEM_MESSAGE); return;}
    }
    else if(hex_mode == HEX_EDIT_RAM)
    {
        fd = FD_LV1; pos = lv1_pos;
        hex_filesize = size_lv1 = 0x10000000ULL;
        begin_lv1 = 0;
    }
    else if(hex_mode == HEX_EDIT_LV2)
    {
        fd = FD_LV2; pos = lv2_pos;
        hex_filesize = size_lv2 = 0x800000ULL;
        begin_lv2 = 0;
    }

read_file:

    memset(MEM_HEX_EDIT, 0, 0x180);

    if(fd == FD_LV1 || fd == FD_LV2)
    {
        ret = 0;
        if(fd == FD_LV1) {if(begin_lv1 > pos) ret =(int) 0x8001001E; if(pos >= size_lv1) temp = 0; else  temp = pos;}
        if(fd == FD_LV2) {if(begin_lv2 > pos) ret =(int) 0x8001001E; if(pos >= size_lv2) temp = 0; else  temp = pos;}
    }
    else if(is_ntfs)
    {
        temp = ps3ntfs_seek64(fd, pos, 0);
        if(temp < 0) ret = FAILED; else ret = SUCCESS;
    }
    else
        ret = sysLv2FsLSeek64(fd, pos, 0, &temp);

    if(ret != SUCCESS || pos != temp)
    {
        if(ret == 0) ret = (int) 0x8001001E;
        sprintf(MEM_MESSAGE, "Lseek Error: 0x%08x\n\n%s", ret, getlv2error(ret));
        DrawDialogOK(MEM_MESSAGE);
        readed = 0;
    }
    else
    {
        readed = hex_filesize - pos;
        if(readed > 0x180ULL) readed = 0x180ULL;
        temp = 0;

        if(fd == FD_LV1)
        {
            ret = read_LV1(pos, MEM_HEX_EDIT, (int) readed);
            temp = readed;
        }
        else if(fd == FD_LV2)
        {
            ret = read_LV2(pos, MEM_HEX_EDIT, (int) readed);
            temp = readed;
        }
        else if(is_ntfs)
        {
            ret = ps3ntfs_read(fd, MEM_HEX_EDIT, readed);
            temp = (u64) ret; if(ret>0) ret = 0;
        }
        else
            ret = sysLv2FsRead(fd, MEM_HEX_EDIT, readed, &temp);

        if(ret < 0 || readed != temp)
        {
            if(ret == 0) ret = (int) 0x8001002B;
            sprintf(MEM_MESSAGE, "Read Error: 0x%08x\n\n%s", ret, getlv2error(ret));
            DrawDialogOK(MEM_MESSAGE);
            readed = temp;
        }
    }

    memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);

    strncpy(hex_path, path, strlen(path));

    while(true)
    {

        draw_hex_editor();

        if(function_menu == HEX_GOTO_ADDRESS || function_menu == HEX_FIND_VALUE)
        {
            px = 64;
            py = 64 + 16;

            SetFontSize(8, 16);
            DrawBox(px, py, 0, 4 * 40 + 4, 4 * 40 + 8 + 32, GRAY);

            SetFontColor(BLACK, INVISIBLE);
            if(function_menu == HEX_GOTO_ADDRESS)
                DrawFormatString(px + 4, py + 4, "Go to Address");
            else
                DrawFormatString(px + 4, py + 4, "Find Hex Values");

            SetFontColor(BLACK, WHITE);

            py += 16;

            DrawFormatString(px + 20, py + 4, "                ");

            for(n = 0; n < f_len; n++)
            {
                if(f_pos == n  && (frame & BLINK))
                    SetFontColor(BLACK, 0x00bfcfff);
                else
                    SetFontColor(BLACK, WHITE);

                if(function_menu == HEX_GOTO_ADDRESS)
                    DrawFormatString(px + 20 + (15 - f_len) * 8 + n * 8, py + 4, "%X", (n & 1) ? (temp_buffer[0x1000 + (n>>1)] & 15) : (temp_buffer[0x1000 + (n>>1)] >> 4));
                else
                    DrawFormatString(px + 20 + n * 8, py + 4, "%X", (n & 1) ? (find[n>>1] & 15) : (find[n>>1] >> 4));
            }

            py += 20;

            SetFontSize(32, 32);

            for(n = 0; n < 4; n++)
            {
                for(m = 0; m < 4; m++)
                {
                    if((f_key & 3) == m && ((f_key>>2) & 3) == n && (frame & BLINK))
                        SetFontColor(BLACK, 0x00bfcfff);
                    else
                        SetFontColor(BLACK, WHITE);

                    DrawFormatString(px + 4 + m * 40, py + 4 + n * 40, "%X", ((n<<2) | m));
                }
            }

            SetFontColor(WHITE, INVISIBLE);
            SetFontSize(8, 16);
        }

        if(enable_menu && function_menu == HEX_EDIT_MODE)
        {
            int py = 0;

            if(new_pad & BUTTON_CROSS_) frame = 300;

            DrawBox((848 - 224)/2, (512 - 248 - 24)/2, 0, 224, 248 - 24, GRAY);
            DrawBox((848 - 216)/2, (512 - 240 - 24)/2, 0, 216, 240 - 24, POPUPMENUCOLOR);
            set_ttf_window((848 - 200)/2, (512 - 240 - 24)/2, 200, 240 - 24, 0);

            display_ttf_string(0, py, "Go to Address",         (enable_menu == 1 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Find Hex",              (enable_menu == 2 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Find String",           (enable_menu == 3 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Find String (no case)", (enable_menu == 4 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Find Hex from Data",    (enable_menu == 5 && (frame & BLINK)) ? INVISIBLE : copy_len ? WHITE: GRAY, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Mark Begin",            (enable_menu == 6 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Mark End",              (enable_menu == 7 && (frame & BLINK)) ? INVISIBLE : (mark_flag == 1) ? WHITE : GRAY, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Copy Mark Area",        (enable_menu == 8 && (frame & BLINK)) ? INVISIBLE : (mark_flag == 2) ? WHITE : GRAY, 0, 16, 24); py += 24;

            display_ttf_string(0, py, "Paste Copied Data",     (enable_menu == 9 && (frame & BLINK)) ? INVISIBLE : copy_len ? WHITE: GRAY, 0, 16, 24); py += 24;

        }

        modified = (!read_only && memcmp(MEM_HEX_READ, MEM_HEX_EDIT, 0x180));

        if(help)
        {
            DrawBox((848 - 624)/2, (512 - 424)/2, 0, 624, 424, GRAY);
            DrawBox((848 - 616)/2, (512 - 416)/2, 0, 616, 416, POPUPMENUCOLOR);
            set_ttf_window((848 - 600)/2, (512 - 416)/2, 600, 416, WIN_AUTO_LF);

            if(enable_menu && function_menu == HEX_EDIT_MODE)    display_ttf_string(0, 0, help2, WHITE, 0, 16, 24); else
            if(               function_menu == HEX_GOTO_ADDRESS) display_ttf_string(0, 0, help4, WHITE, 0, 16, 24); else
            if(               function_menu == HEX_FIND_VALUE)   display_ttf_string(0, 0, help5, WHITE, 0, 16, 24); else
                                                                 display_ttf_string(0, 0, help3, WHITE, 0, 16, 24);
        }


        if(help && (new_pad & BUTTON_START))
        {
            help = 0;
            start_status = 0;
        }

        if(start_status <= 180 && (old_pad & BUTTON_SELECT))
        {
            start_status++;
            if(start_status > 180) help = 1;

            if(new_pad & BUTTON_START)
            {
                //cancel without any change
                if(hex_mode == HEX_EDIT_RAM) lv1_pos = pos; else
                if(hex_mode == HEX_EDIT_LV2) lv2_pos = pos;

                break;
            }
        }
        if(enable_menu && (new_pad & BUTTON_SELECT)) help = 1;



        if(help && (new_pad & BUTTON_CIRCLE_))  {help ^= 1; start_status = 0; new_pad ^= BUTTON_CIRCLE_;}
        if(help && (new_pad & BUTTON_TRIANGLE)) {help ^= 1; start_status = 0; new_pad ^= BUTTON_TRIANGLE;}

        if(help) continue;


        if(!enable_menu && (new_pad & BUTTON_CIRCLE_))
        {
            if(old_pad & BUTTON_SELECT)
            {
                //cancel without any change
                if(hex_mode == HEX_EDIT_RAM) lv1_pos = pos; else
                if(hex_mode == HEX_EDIT_LV2) lv2_pos = pos;

                break;
            }
            else
            {
                if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                {
                    save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                    memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                    modified = false;
                }

                if((modified == false) || DrawDialogYesNo("Exit from Hex Editor?") == YES)
                {
                    if(hex_mode == HEX_EDIT_RAM) lv1_pos = pos; else
                    if(hex_mode == HEX_EDIT_LV2) lv2_pos = pos;

                    break;
                }
            }
        }

        if(!enable_menu)
        {
            AUTO_BUTTON_REP2(auto_up, BUTTON_UP)
            AUTO_BUTTON_REP2(auto_down, BUTTON_DOWN)
            AUTO_BUTTON_REP2(auto_left, BUTTON_LEFT)
            AUTO_BUTTON_REP2(auto_right, BUTTON_RIGHT)
            AUTO_BUTTON_REP2(auto_l2, BUTTON_L2)
            AUTO_BUTTON_REP2(auto_r2, BUTTON_R2)
            AUTO_BUTTON_REP2(auto_l1, BUTTON_L1)
            AUTO_BUTTON_REP2(auto_r1, BUTTON_R1)

            if((new_pad & BUTTON_R3) && find_len)
            {
                if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                {
                    save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                    memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                    modified = false;
                }
                if(!modified)
                {
                    u64 found;

                    found = pos + (u64) ((e_y * 0x10) + (e_x>>1) + 1);
                    if(found >= hex_filesize) found = 0ULL;
                    find_in_file(is_ntfs, fd, found, hex_filesize, &found, find, find_len, 1);

                    enable_menu = function_menu = HEX_EDIT_MODE;

                    if(found == TEXTNOTFOUND)
                    {
                        if(find_mode == FIND_HEX_MODE)
                            DrawDialogOKTimer("Hex String not found", 2000.0f);
                        else
                            DrawDialogOKTimer("String not found", 2000.0f);
                    }
                    else
                    {
                        pos = found & ~15ULL;
                        e_y = 0;
                        e_x = (found & 15) << 1;
                        goto read_file;
                    }
                }
            }

            if((new_pad & BUTTON_L3) && find_len)
            {
                if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                {
                    save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                    memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                    modified = false;
                }
                if(!modified)
                {
                    u64 found;

                    found = pos + (u64) ((e_y * 0x10) + (e_x>>1));
                    if(found >= hex_filesize) found = 0ULL;
                    find_in_file(is_ntfs, fd, found, hex_filesize, &found, find, find_len, -1);

                    enable_menu = function_menu = HEX_EDIT_MODE;

                    if(found == TEXTNOTFOUND)
                    {
                        if(find_mode == FIND_HEX_MODE)
                            DrawDialogOKTimer("Hex String not found", 2000.0f);
                        else
                            DrawDialogOKTimer("String not found", 2000.0f);
                    }
                    else
                    {
                        pos = found & ~15ULL;
                        e_y = 0;
                        e_x = (found & 15) << 1;
                        goto read_file;
                    }
                }
            }

            if(new_pad & BUTTON_UP)
            {
                auto_up = 1;
                e_y--;
                if(e_y < 0)
                {
                    e_y = 0;

                    if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                    {
                        save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                        memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                        modified = false;
                    }

                    if(!modified)
                    {
                        if(pos >= 16ULL)  pos -= 16ULL;
                        else
                        {
                            if(hex_filesize>= 16ULL)
                                pos = (hex_filesize - 16ULL) & ~(15ULL);
                            else
                                pos = 0;
                        }
                        goto read_file;
                    }
                }
            }
            else if(new_pad & BUTTON_DOWN)
            {
                auto_down = 1;
                e_y++;
                if(e_y > 23)
                {
                    e_y = 23;

                    if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                    {
                        save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                        memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                        modified = false;
                    }

                    if(!modified)
                    {
                        if(pos + 16ULL < hex_filesize)  pos += 16ULL;
                        else pos = 0ULL;
                        goto read_file;
                    }
                }
            }
            else if(new_pad & BUTTON_LEFT)
            {
                auto_left = 1;
                e_x--;
                if(e_x < 0)
                {
                    e_x = 0x1f;
                    e_y--;
                    if(e_y < 0)
                    {
                        e_y = 0;
                        if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                        {
                            save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                            memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                            modified = false;
                        }

                        if(!modified)
                        {
                            if(pos >= 16ULL)  pos -= 16ULL;
                            else
                            {
                                if(hex_filesize >= 16ULL)
                                    pos = (hex_filesize - 16ULL) & ~(15ULL);
                                else
                                    pos = 0;
                            }
                            goto read_file;
                        }
                    }
                }
            }
            else if(new_pad & BUTTON_RIGHT)
            {
                auto_right = 1;
                e_x++;
                if(e_x > 0x1f)
                {
                    e_x = 0;
                    e_y++;
                    if(e_y > 23)
                    {
                        e_y = 23;
                        if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                        {
                            save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                            memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                            modified = false;
                        }
                        if(!modified)
                        {
                            if(pos + 16ULL < hex_filesize)  pos += 16ULL;
                            else pos = 0ULL;
                            goto read_file;
                        }
                    }
                }
            }

            if((new_pad & BUTTON_L1)) // scroll up
            {
                u64 incre = 0x80ULL;

                if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                {
                    save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                    memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                    modified = false;
                }

                auto_l11++;
                start_status = 0;
                if((old_pad & BUTTON_SELECT))
                    incre = 0x1000ULL;
                else
                    incre <<= 4 * (auto_l11 / 10);

                if(incre > 0x6400000ULL) incre = 0x6400000ULL;

                auto_l1 = 1;
                if(pos >= incre)  pos -= incre;
                else
                {
                    if(hex_filesize >= 16ULL)
                        pos = (hex_filesize - 16ULL) & ~(15ULL);
                    else pos = 0;
                }
                goto read_file;

            }
            else if(!(old_pad & BUTTON_L1)) auto_l11 = 0;

            if((new_pad & BUTTON_R1)) // scroll down
            {
                u64 incre = 0x80ULL;

                if(modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
                {
                    save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                    memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                    modified = false;
                }

                auto_r11++;
                start_status = 0;
                if((old_pad & BUTTON_SELECT))
                    incre = 0x1000ULL;
                else
                    incre <<= 4 * (auto_r11 / 10);

                if(incre > 0x6400000ULL) incre = 0x6400000ULL;

                auto_r1 = 1;
                if(pos + incre < hex_filesize)  pos += incre;
                else pos = 0ULL;

                goto read_file;
            } else if(!(old_pad & BUTTON_R1)) auto_r11 = 0;

        /**********************************************************************************************************/
        /* MODIFICATION AREA                                                                                      */
        /**********************************************************************************************************/

             // byte ++
            if((new_pad & BUTTON_R2) && !read_only)
            {
               u8 * p = (u8 *) &temp_buffer[HEX_EDIT + (e_y * 0x10) + (e_x>>1)];
                if(((e_y * 0x10) + (e_x>>1)) < readed)
                {
                    p[0] = (p[0] + 1);
                }
                auto_r2 = 1;
            }

            // byte --
            if((new_pad & BUTTON_L2) && !read_only)
            {
                u8 * p = (u8 *) &temp_buffer[HEX_EDIT + (e_y * 0x10) + (e_x>>1)];
                if(((e_y * 0x10) + (e_x>>1)) < readed)
                {
                    p[0] = (p[0] - 1);
                }

                auto_l2 = 1;
            }

            // nibble ++
            if((new_pad & BUTTON_CROSS_) && !read_only)
            {
               u8 * p = (u8 *) &temp_buffer[HEX_EDIT + (e_y * 0x10) + (e_x>>1)];
                if(((e_y * 0x10) + (e_x>>1)) < readed)
                {
                    if(e_x & 1)
                        p[0] = ((p[0] + 1) & 0xf) | (p[0] & 0xf0);
                    else
                        p[0] = ((p[0] + 0x10) & 0xf0) | (p[0] & 0xf);
                }
            }

            // nibble --
            if((new_pad & BUTTON_TRIANGLE) && !read_only)
            {
                u8 * p = (u8 *) &temp_buffer[HEX_EDIT + (e_y * 0x10) + (e_x>>1)];
                if(((e_y * 0x10) + (e_x>>1)) < readed)
                {
                    if(e_x & 1)
                        p[0] = ((p[0] - 1) & 0xf) | (p[0] & 0xf0);
                    else
                        p[0] = ((p[0] - 0x10) & 0xf0) | (p[0] & 0xf);
                }
            }

            // undo all
            if(((old_pad & BUTTON_SELECT) && (new_pad & BUTTON_SQUARE)) && !read_only)
            {
                memcpy(MEM_HEX_EDIT, MEM_HEX_READ, 0x180);
            }
            // undo one
            else if((new_pad & BUTTON_SQUARE) && !read_only)
            {
                if(((e_y * 0x10) + (e_x>>1)) < readed)
                {
                    if(temp_buffer[HEX_EDIT + (e_y * 0x10) + (e_x>>1)] == temp_buffer[HEX_READ + (e_y * 0x10) + (e_x>>1)])
                        {function_menu = (mark_flag == 1 && (pos + (u64) ((e_y * 0x10) + (e_x>>1))) >= mark_ini) ? 7 : 6; enable_menu = help = start_status = 0; goto edit_options;}
                    else
                        temp_buffer[HEX_EDIT + (e_y * 0x10) + (e_x>>1)] = temp_buffer[HEX_READ + (e_y * 0x10) + (e_x>>1)];
                }
            }


        } // enable menu off
        else
        {// enable menu on
            if(function_menu == HEX_FIND_VALUE)
            {
                if(new_pad & BUTTON_R1)
                {
                    //auto_r1 = 1;
                    memset((char *) &find[f_len>>1], 0, 8);
                    f_len+=2;
                    if(f_len > 16) f_len = 16;
                    if(f_pos >= f_len) f_pos = (f_len) - 1;
                }
                else if(new_pad & BUTTON_L1)
                {
                    //auto_l1 = 1;
                    memset((char *) &find[f_len>>1], 0, 8);
                    f_len-=2;
                    if(f_len < 2) f_len = 2;
                    if(f_pos >= f_len) f_pos = f_len - 1;
                }
            }

            if(function_menu == HEX_GOTO_ADDRESS || function_menu == HEX_FIND_VALUE)
            {
                if(new_pad & BUTTON_R2)
                {
                    //auto_r2 = 1;
                    f_pos++;
                    if(f_pos >= f_len) f_pos = (f_len) - 1;
                }
                else if(new_pad & BUTTON_L2)
                {
                    //auto_l2 = 1;
                    f_pos--;
                    if(f_pos < 0) f_pos = 0;
                }
                else if(new_pad & BUTTON_UP)
                {
                    //auto_up = 1;
                    if((f_key & 12) == 0) f_key|=12; else f_key-=4;
                }
                else if(new_pad & BUTTON_DOWN)
                {
                    //auto_down = 1;
                    if((f_key & 12) == 12) f_key=12; else f_key+=4;
                }
                else if(new_pad & BUTTON_LEFT)
                {
                    //auto_left = 1;
                    if((f_key & 3) == 0) f_key|=3; else f_key--;
                }
                else if(new_pad & BUTTON_RIGHT)
                {
                    //auto_right = 1;
                    if((f_key & 3) == 3) f_key^=3; else f_key++;
                }
                else if(new_pad & BUTTON_CROSS_)
                {
                    u8 * p = (function_menu == HEX_GOTO_ADDRESS) ? (u8 *) &temp_buffer[0x1000 + (f_pos >> 1)] : &find[f_pos >> 1];
                    if(f_pos & 1)
                        p[0] = (f_key) | (p[0] & 0xf0);
                    else
                        p[0] = ((f_key<<4) & 0xf0) | (p[0] & 0xf);

                    if(function_menu == HEX_GOTO_ADDRESS && f_len < 16 && f_pos == (f_len - 1)) f_len++;
                    f_pos++;
                    if(f_pos >= f_len) f_pos = (f_len) - 1;
                }
            }

            if(function_menu == HEX_GOTO_ADDRESS && (new_pad & BUTTON_SQUARE))
            {
                f_len--;
                if(f_len < 1) f_len = 1;
                else {
                    u8 * p = (u8 *) &temp_buffer[0x1000 + (f_len >> 1)];
                    // clear the nibble
                    if(f_len & 1)
                        p[0] = (p[0] & 0xf0);
                    else
                        p[0] = (p[0] & 0xf);
                }
                if(f_pos >= f_len) f_pos = (f_len) - 1;
            }
            else if((function_menu == HEX_GOTO_ADDRESS || function_menu == HEX_FIND_VALUE) && (new_pad & BUTTON_START))
            {
                switch(function_menu)
                {
                    case 1:
                    {
                        pos = 0ULL;
                        memcpy(((char *) &pos), &temp_buffer[0x1000], (f_len+1)/2);

                        //if(!(f_len & 1))
                        pos>>=(u64) ((16 - f_len) <<2);

                        if(pos >= hex_filesize) pos = 0ULL;

                        e_y = 0; e_x = 0;
                        pos &= ~15ULL;
                        enable_menu = function_menu = HEX_EDIT_MODE;
                        goto read_file;
                        break;
                    }
                    case 2:
                    {
                        u64 found;

                        find_len = f_len / 2;

                        found = pos + (u64) ((e_y * 0x10) + (e_x>>1) + 1);
                        if(found >= hex_filesize) found = 0ULL;
                        find_mode = FIND_HEX_MODE;
                        find_in_file(is_ntfs, fd, found, hex_filesize, &found, find, find_len, 1);

                        enable_menu = function_menu = HEX_EDIT_MODE;

                        if(found == TEXTNOTFOUND)
                        {
                            DrawDialogOK("Hex string not found");
                        }
                        else
                        {
                            pos = found & ~15ULL;
                            e_y = 0;
                            e_x = (found & 15) << 1;
                            goto read_file;
                        }
                        break;
                    }
                }
            }

            if(function_menu == HEX_EDIT_MODE)
            {
                if(new_pad & BUTTON_UP)
                {
                    if(enable_menu > 1) enable_menu--;  else {enable_menu = 9;}
                }
                else if(new_pad & BUTTON_DOWN)
                {
                    if(enable_menu < 9) enable_menu++;  else {enable_menu = 1;}
                }
                else if(new_pad & BUTTON_CROSS_)
                {
                    function_menu = enable_menu;
edit_options:
                    switch(function_menu)
                    {
                        case 1:
                            memset(&temp_buffer[0x1000], 0, 8);
                            f_len = 1;
                            break;

                        case 2:
                            f_len = 8;
                            if(find_len > 8) find_len = 8;
                            break;
                        case 3:
                            memset(find, 0, 512); find_len = 0;
                            if(Get_OSK_String("Find String", (char *) find, 250) == SUCCESS)
                            {
                                u64 found;

                                find_len = strlen((char *) find);

                                if(find_len != 0)
                                {
                                    found = pos + (u64) ((e_y * 0x10) + (e_x>>1) + 1);
                                    if(found >= hex_filesize) found = 0ULL;
                                    find_mode = FIND_TEXT_MODE;
                                    find_in_file(is_ntfs, fd, found, hex_filesize, &found, find, find_len, 1);

                                    enable_menu = function_menu = HEX_EDIT_MODE;

                                    if(found == TEXTNOTFOUND)
                                    {
                                        DrawDialogOK("String not found");
                                    }
                                    else
                                    {
                                        pos = found & ~15ULL;
                                        e_y = 0;
                                        e_x = (found & 15) << 1;
                                        goto read_file;
                                    }
                                }
                            }
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            break;
                        case 4:
                            memset(find, 0, 512); find_len = 0;
                            if(Get_OSK_String("Find String (no case sensitive)", (char *) find, 250) == SUCCESS)
                            {
                                u64 found;

                                find_len = strlen((char *) find);

                                if(find_len != 0)
                                {
                                    found = pos + (u64) ((e_y * 0x10) + (e_x>>1) + 1);
                                    if(found >= hex_filesize) found = 0ULL;
                                    find_mode = FIND_CASE_INSENSITIVE_MODE;
                                    find_in_file(is_ntfs, fd, found, hex_filesize, &found, find, find_len, 1);

                                    enable_menu = function_menu = HEX_EDIT_MODE;

                                    if(found == TEXTNOTFOUND)
                                    {
                                        DrawDialogOK("String (no case sensitive) not found");
                                    }
                                    else
                                    {
                                        pos = found & ~15ULL;
                                        e_y = 0;
                                        e_x = (found & 15) << 1;
                                        goto read_file;
                                    }
                                }
                            }
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            break;
                        case 5:
                            if(copy_mem && copy_len)
                            {
                                find_len = (copy_len > 512) ? 512 : copy_len;
                                memcpy(find, copy_mem, find_len);

                                u64 found;

                                if(find_len != 0)
                                {
                                    found = pos + (u64) ((e_y * 0x10) + (e_x>>1) + 1);
                                    if(found >= hex_filesize) found = 0ULL;
                                    find_mode = FIND_HEX_MODE;
                                    find_in_file(is_ntfs, fd, found, hex_filesize, &found, find, find_len, 1);

                                    enable_menu = function_menu = HEX_EDIT_MODE;

                                    if(found == TEXTNOTFOUND)
                                    {
                                        DrawDialogOK("Hex string not found");
                                    }
                                    else
                                    {
                                        pos = found & ~15ULL;
                                        e_y = 0;
                                        e_x = (found & 15) << 1;
                                        goto read_file;
                                    }
                                }
                            }
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            break;

                        case 6:
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            if(pos + (u64) ((e_y * 0x10) + (e_x>>1)) >= hex_filesize)
                            {
                                DrawDialogOKTimer("Mark is out of filesize / memory", 2000.0f);
                            }
                            else
                            {
                                mark_ini = pos + (u64) ((e_y * 0x10) + (e_x>>1));
                                mark_flag = 1;
                            }
                            break;

                        case 7:
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            if(!mark_flag) mark_ini = 0;

                            if((pos + (u64) ((e_y * 0x10) + (e_x>>1))) >= mark_ini &&
                               (pos + (u64) ((e_y * 0x10) + (e_x>>1))) < (mark_ini + 0x100000ULL))
                            {
                                if(pos + (u64) ((e_y * 0x10) + (e_x>>1)) >= hex_filesize)
                                {
                                    DrawDialogOKTimer("Mark is out of file size / memory: truncating to the end position", 2000.0f);
                                    mark_len = hex_filesize - mark_ini + 1ULL;
                                }
                                else
                                    mark_len = (pos + (u64) ((e_y * 0x10) + (e_x>>1))) - mark_ini + 1ULL;

                                mark_flag = 2;
                            }
                            else DrawDialogOKTimer("Mark position out of the range\nyou can select a block of 1 MB max from Mark Begin", 2000.0f);
                            break;

                        case 8:
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            if(mark_flag == 2) {
                                if(copy_mem) free(copy_mem);
                                copy_mem = malloc(mark_len);
                                copy_len = 0;
                                if(!copy_mem) DrawDialogOKTimer("Out of memory from copy function", 2000.0f);
                                else {copy_len = mark_len;

                                    if(load_hex(is_ntfs, fd, mark_ini, copy_mem, mark_len) == 0) {
                                        sprintf(TEMP_PATH2, "Copied %d bytes", copy_len);
                                        DrawDialogOKTimer(TEMP_PATH2, 2000.0f);
                                    }
                                }
                            } else DrawDialogOKTimer("Nothing to Copy", 2000.0f);


                            break;

                        case 9:
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            if(copy_len == 0 || !copy_mem) {DrawDialogOKTimer("Paste buffer is empty", 2000.0f);}
                            //else if(fd != FD_LV1 && fd != FD_LV2) DrawDialogOKTimer("Paste is Only supported to memory for now", 2000.0f);
                            else {
                                u64 my_pos = (pos + (u64) ((e_y * 0x10) + (e_x>>1)));
                                int my_len = copy_len;

                                if((my_pos + (u64) my_len) > hex_filesize)
                                {
                                     my_len = (u32) (hex_filesize - my_pos);
                                     sprintf(MEM_MESSAGE, "Paste buffer exceeds %d bytes the file / memory\n\nWant you write %d bytes from 0x%08X%08X ?", copy_len - my_len, my_len, (u32) (my_pos>>32), (u32) my_pos);
                                }
                                else
                                {
                                    sprintf(MEM_MESSAGE, "Do you want to write %d bytes from 0x%08X%08X ?", my_len, (u32) (my_pos>>32), (u32) my_pos);
                                }

                                if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                                {
                                    int ret = 0;

                                    ret = save_hex(is_ntfs, fd, my_pos, copy_mem, my_len);

                                    if(ret == 0)
                                    {
                                        sprintf(MEM_MESSAGE, "%d bytes written", my_len);
                                        DrawDialogOKTimer(MEM_MESSAGE, 2000.0f);
                                    }

                                    goto read_file;
                                }
                            }

                            break;

                        case 10:
                            enable_menu = function_menu = HEX_EDIT_MODE;

                            f_key = 0;
                            f_pos = 0;
                            f_len = (find_len > 8) ? 16 : find_len * 2;

                            break;
                        default:
                            enable_menu = function_menu = HEX_EDIT_MODE;
                            break;
                    }
                }
            } // func menu 0

        } // enable menu on

        if((enable_menu == 0 && (new_pad & BUTTON_START)) ||
           (enable_menu != 0 && (new_pad & (BUTTON_CIRCLE_ | BUTTON_TRIANGLE))))
        {
            enable_menu = !enable_menu;
            function_menu = HEX_EDIT_MODE;

            f_key = 0;
            f_pos = 0;
            f_len = (find_len > 8) ? 16 : find_len * 2;

            if(enable_menu && modified && DrawDialogYesNo("Do you want to save the changes?") == YES)
            {
                save_hex(is_ntfs, fd, pos, MEM_HEX_EDIT, readed);
                memcpy(MEM_HEX_READ, MEM_HEX_EDIT, 0x180);
                modified = false;
            }

            // if modified undo all changes
            if(modified) {memcpy(MEM_HEX_EDIT, MEM_HEX_READ, 0x180); modified = false;}
        }

    }

    if(fd >= SUCCESS)
    {
        if(is_ntfs) ps3ntfs_close(fd); else  sysLv2FsClose(fd);
    }

    fd = FAILED;
    frame = 0;
}
#endif

/***********************************************************************************************************/
/* COBRA ISO                                                                                               */
/***********************************************************************************************************/

void fun_exit();

bool is_retro_file(char *rom_path, char *rom_file)
{
    if(strlen(retro_root_path) > 0 && strcasestr(rom_path, retro_root_path) == NULL) return false;

    sprintf(rom_extension, "%s", get_extension(rom_file));
    if(strlen(rom_extension) < 2) return false;

    strtoupper(rom_extension);
    strcat(rom_extensions, " ");

    return (strlen(rom_extension) > 0 && strcasestr(rom_extensions, rom_extension) != NULL);
}

#ifdef LOADER_MODE
void launch_ps2classic(char *ps2iso_path, char *ps2iso_title) {}
void launch_retro(char *rom_path) {}
void launch_video(char *videofile) {}
#else
void launch_ps2classic(char *ps2iso_path, char *ps2iso_title)
{
    if(file_exists(PS2_CLASSIC_PLACEHOLDER))
    {
        int ret = FAILED;

        if(strcmp(temp_buffer, PS2_CLASSIC_ISO_PATH))
        {
            sprintf(MEM_MESSAGE, "%s\n\nDo you want to copy the PS2 image to PS2 Classics Placeholder?", ps2iso_title);

            if(DrawDialogYesNo(MEM_MESSAGE) == YES)
            {
                sprintf(temp_buffer, "%s", ps2iso_path);

                unlink_secure(PS2_CLASSIC_ISO_PATH);
                ret = CopyFile(temp_buffer, PS2_CLASSIC_ISO_PATH);

                if(ret == SUCCESS)
                {
                    if(firmware>=0x465C)
                        SaveFile("/dev_hdd0/classic_ps2", (char *)temp_buffer, 0);

                    temp_buffer[strlen(temp_buffer) - 4] = 0;
                    strcat(temp_buffer, ".png");
                    if(file_exists(temp_buffer))
                    {
                        unlink_secure(PS2_CLASSIC_ISO_ICON);
                        ret = CopyFile(temp_buffer, PS2_CLASSIC_ISO_ICON);
                    }
                    else
                    {
                        temp_buffer[strlen(temp_buffer) - 4] = 0;
                        strcat(temp_buffer, ".PNG");
                        if(file_exists(temp_buffer))
                        {
                            unlink_secure(PS2_CLASSIC_ISO_ICON);
                            ret = CopyFile(temp_buffer, PS2_CLASSIC_ISO_ICON);
                        }
                        else
                        {
                            temp_buffer[strlen(temp_buffer) - 8] = 0;
                            strcat(temp_buffer, ".png");
                            if(file_exists(temp_buffer))
                            {
                                unlink_secure(PS2_CLASSIC_ISO_ICON);
                                ret = CopyFile(temp_buffer, PS2_CLASSIC_ISO_ICON);
                            }
                            else
                            {
                                temp_buffer[strlen(temp_buffer) - 4] = 0;
                                strcat(temp_buffer, ".PNG");
                                if(file_exists(temp_buffer))
                                {
                                    unlink_secure(PS2_CLASSIC_ISO_ICON);
                                    ret = CopyFile(temp_buffer, PS2_CLASSIC_ISO_ICON);
                                }
                            }
                        }
                    }
                }
            }
        }
        else
            ret = SUCCESS;

        if(ret)
            DrawDialogOKTimer("ERROR: PS2 image could not be copied to PS2 Classics Placeholder", 5000.0f);
        else if(DrawDialogYesNoDefaultYes("Do you want to exit to XMB to launch the mounted game with PS2 Classics Placeholder?") == YES)
        {
            // Save game list
            fun_exit();
            SaveGameList();

            exit(0);
        }
    }
    else
        DrawDialogOKTimer("PS2 Classics Placeholder must be installed", 3000.0f);
}

void launch_retro(char *rom_path)
{
     char emu_path[MAXPATHLEN];

     sprintf(emu_path, "%s/USRDIR/EBOOT.BIN", retroarch_path);
     if(file_exists(emu_path) == false)
     {
         DrawDialogOKTimer("ERROR: RetroArch is not installed.\nCannot launch the selected Retro game.", 3000.0f);
         return;
     }

     char src_path[MAXPATHLEN];
     char dst_path[MAXPATHLEN];
     char libretro_rom_path[MAXPATHLEN + 32];

     sprintf(emu_path, "%s/USRDIR/RETRO.self", self_path);
     if(file_exists(emu_path) == false)
     {
         DrawDialogOKTimer("ERROR: RETRO.self was not found.\nCannot launch the selected Retro game.", 3000.0f);
         return;
     }

     // Clean temporary roms path
     sprintf(dst_path, "%s/USRDIR/cores/roms", self_path);
     DeleteDirectory(dst_path);
     mkdir_secure(dst_path);

     // Get rom path
     sprintf(src_path, "%s", rom_path);

     if(is_ntfs_path(rom_path))
     {
         sprintf(dst_path, "%s/USRDIR/cores/roms/%s", self_path, get_filename(src_path));

         unlink_secure(dst_path);
         CopyFile(src_path, dst_path);
     }
     else
         sprintf(dst_path, "%s", rom_path);

     if(file_exists(dst_path))
     {
         // Copy prboom.wad to rom path
         if(strlen(retro_doom_path) > 0 && strstr(rom_path, retro_doom_path))
         {
             char wad_path[MAXPATHLEN];
             strcpy(wad_path, dst_path);

             int p = strlen(wad_path);
             while (p > 0 && wad_path[p] != '/') p--;

             strcpy(wad_path + p, "/prboom.wad");

             if(file_exists((char *)wad_path) == false)
             {
                 sprintf(libretro_rom_path, "%s/USRDIR/cores/system/prboom.wad", self_path);
                 if(file_exists((char *)libretro_rom_path)) CopyFile(libretro_rom_path, wad_path);
             }
         }

        // Set rom path
        sprintf(libretro_rom_path, "libretro_rom_path = \"%s\"\n", dst_path);

        // Select template
        if(strcasestr(src_path, retro_snes_path) != NULL || strcasestr(src_path, "/ROMS/snes/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/snes-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_gba_path) != NULL || strcasestr(src_path, "/ROMS/gba/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/gba-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_gen_path) != NULL || strcasestr(src_path, "/ROMS/gen/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/gen-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_nes_path) != NULL || strcasestr(src_path, "/ROMS/fceu/") != NULL)
        {
            if(!strcmpext(src_path, ".fds"))
                sprintf(src_path, "%s/USRDIR/cores/fds-retroarch.cfg", self_path);
            else
                sprintf(src_path, "%s/USRDIR/cores/nes-retroarch.cfg", self_path);
        }
        else if(strcasestr(src_path, retro_mame_path) != NULL || strcasestr(src_path, "/ROMS/mame/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/mame-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_fba_path) != NULL || strcasestr(src_path, "/ROMS/fba/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/fba-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_doom_path) != NULL || strcasestr(src_path, "/ROMS/prb/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/doom-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_quake_path) != NULL || strcasestr(src_path, "/ROMS/pak/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/quake-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_pce_path) != NULL || strcasestr(src_path, "/ROMS/pce/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/pce-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_gb_path) != NULL || strcasestr(src_path, "/ROMS/gb") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/gbc-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_gbc_path) != NULL || strcasestr(src_path, "/ROMS/snes/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/gbc-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_atari_path) != NULL || strcasestr(src_path, "/ROMS/atari/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/atari-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_vb_path) != NULL || strcasestr(src_path, "/ROMS/voy/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/vb-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_nxe_path) != NULL || strcasestr(src_path, "/ROMS/nxe/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/nxe-retroarch.cfg", self_path);
        else if(strcasestr(src_path, retro_wswan_path) != NULL || strcasestr(src_path, "/ROMS/wsw/") != NULL)
            sprintf(src_path, "%s/USRDIR/cores/wswan-retroarch.cfg", self_path);
        else
        {
            DrawDialogOKTimer("ERROR: Invalid path for Retro game.", 3000.0f);
            return;
        }

        // Remove old retroarch.cfg
        sprintf(dst_path, "%s/USRDIR/retroarch.cfg", self_path);
        unlink_secure(dst_path);

        // Create new retroarch.cfg
        FILE *fp;

        // write rom path
        fp = fopen(dst_path, "w");
        fputs (libretro_rom_path, fp);
        fclose(fp);

        // Load template
        int size;
        char *template_cfg = LoadFile(src_path, &size);

        if(!template_cfg)
        {
            DrawDialogOKTimer("ERROR: Could not load the config file for the emulator.", 3000.0f);
            return;
        }

        // append template
        fp = fopen(dst_path, "a");
        fputs (template_cfg, fp);
        fclose(fp);

        free(template_cfg);

        // Save game list
        fun_exit();
        SaveGameList();

        // call emulator
        sysProcessExitSpawn2(emu_path, NULL, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
        exit(0);
     }
     else
         DrawDialogOKTimer("ERROR: Cannot launch the selected Retro game.", 3000.0f);
}

void launch_video(char *videofile)
{
    char flist[MAXPATHLEN];

    sprintf(flist, "%s/USRDIR/TEMP", self_path);
    mkdir_secure(flist);

    sprintf(flist, "%s/USRDIR/TEMP/SHOWTIME.TXT", self_path);
    unlink_secure(flist);

    if(is_ntfs_path(videofile)) return;

    char my_video_file[1024];
    snprintf(my_video_file, 1020, videofile);

    char filename[1024];
    sprintf(filename, "file://%s", my_video_file);

    FILE *fd;

    fd = fopen(flist, "w");
    fputs (filename, fd);
    fclose(fd);

    launch_showtime(true);
}
#endif

void launch_showtime(bool playmode)
{
    char stself[1024];

    if(!playmode)
    {
        sprintf(stself, "%s/USRDIR/TEMP/SHOWTIME.TXT", self_path);
        unlink_secure(stself);
    }

    sprintf(stself, "%s/USRDIR/SHOWTIME.SELF", self_path);

    if(file_exists(stself) == false) sprintf(stself, "/dev_hdd0/game/IRISMAN00/USRDIR/USRDIR/SHOWTIME.SELF");
    if(file_exists(stself) == false) sprintf(stself, "%s/USRDIR/sys/SHOWTIME.SELF", MM_PATH);

    if(file_exists(stself))
    {
        reset_sys8_path_table();
        add_sys8_path_table(MM_PATH, self_path);
        build_sys8_path_table();

        fun_exit();
        SaveGameList();

        sysProcessExitSpawn2((const char*)stself, NULL, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
        exit(0);
    }

    if(file_exists(MOVIAN))
    {
        fun_exit();
        SaveGameList();

        sysProcessExitSpawn2((const char*)MOVIAN, NULL, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
        exit(0);
    }

    if(file_exists(SHOWTIME))
    {
        fun_exit();
        SaveGameList();

        sysProcessExitSpawn2((const char*)SHOWTIME, NULL, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
        exit(0);
    }
}

#ifdef LOADER_MODE
void launch_luaplayer(char *lua_path) {}
int mount_psp_iso(char *path) {return FAILED;}
int launch_iso_game(char *path, int mtype) {return FAILED;}
int launch_iso_game_mamba(char *path, int mtype) {return FAILED;}
int launch_iso_build(char *iso_path, char *src_path, bool run_showtime) {return FAILED;}
#else
void launch_luaplayer(char *lua_path)
{
    sysFSStat stat;

    char luaplayer[1024];
    sprintf(luaplayer, "%s/USRDIR/LuaPlayer.self", self_path);

    if(sysLv2FsStat(luaplayer, &stat) == SUCCESS)
    {
        char temp_lua[1024];
        sprintf(temp_lua, "%s/USRDIR/app.lua", self_path);

        if(strcmp(lua_path, temp_lua))
        {
            unlink_secure(temp_lua);
            CopyFile(lua_path, temp_lua);
        }

        fun_exit();
        SaveGameList();

        sysProcessExitSpawn2((const char*)luaplayer, NULL, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
        exit(0);
    }
}

int mount_psp_iso(char *path)
{
    char icon_path[MAXPATHLEN];
    sprintf(icon_path, "%s/PIC1.PNG", psp_launcher_path);

    unlink_secure((char*) icon_path);
    cobra_unset_psp_umd();

    sprintf(icon_path, "%s/USRDIR/icons/PSP_ICON.PNG", self_path);

    int ret = cobra_set_psp_umd2(path, NULL, (char*)icon_path, 2);

    if(ret)
    {
        DrawDialogOKTimer("PSP image could not be mounted", 2000.0f);
        return FAILED;
    }
    else
    {
        DrawDialogOKTimer("Use PSP Remaster Launcher to play the mounted game", 2500.0f);
        cobra_send_fake_disc_insert_event();

        // Save game list
        fun_exit();
        SaveGameList();

        exit(0);
    }
}

int launch_iso_game(char *path, int mtype)
{
    int type = EMU_BD;

    if(is_audiovideo(get_extension(path)))
    {
        launch_video(path);

        //ntfs
        if(is_audiovideo(path) || !strcmpext(path, ".iso") || !strcmpext(path, ".iso.0"))
            type = EMU_BD;
        else
            return FAILED;
    }

    if (use_cobra)
    {
        cobra_umount_disc_image();
        usleep(4000);
        cobra_send_fake_disc_eject_event();
    }

    if((use_cobra && !use_mamba) &&
       (mtype == EMU_PSP || strstr(path, "/PSPISO/") != NULL || strstr(path, "/ISO/") != NULL) &&
       !strcasecmp(path + strlen(path) - 4, ".iso"))
    {
        mount_psp_iso(path);
    }

    int flen = strlen(path) - 4;

    if((strstr(path, "/PSXISO/") != NULL || strstr(path, "/PSXGAMES/") != NULL) &&
       flen >= 0 && (strcasestr(".iso|.bin|.mdf|.img", path + flen) != NULL))
    {
        ps3pad_read();
        if((use_cobra || use_mamba) && (old_pad & BUTTON_SELECT))
        {
            mtype = EMU_PSX; // Mount using Cobra method if launched with SELECT+X
            goto mount_iso;
        }
        else if(is_ntfs_path(path))
        {
            mtype = EMU_PSX; // Mount using Cobra method if PSX ISO is on NTFS/ext
        }
        else
        {
            // Launch PSX ISO directly

            reset_sys8_path_table();

            //syscall36("/dev_bdvd");
            add_sys8_bdvd(NULL, NULL);

            if(lv2peek(0x80000000000004E8ULL) && !use_cobra) syscall_40(1, 0); // disables PS3 Disc-less

            // load PSX options
            sprintf(TEMP_PATH1, "%s", path);
            LoadPSXOptions(TEMP_PATH1);

            if(psx_iso_prepare(TEMP_PATH1, NULL, TEMP_PATH1) == 0)
            {
                return FAILED;
            }

            psx_launch();
            return FAILED;
        }
    }

    if(strstr(path, "/PSXGAMES/") || strstr(path, "/PSXISO/"))
    {
        return launch_iso_game_mamba(path, EMU_PSX);
    }

    if(strstr(path, "/BDISO/"))  return launch_iso_game_mamba(path, EMU_BD);
    if(strstr(path, "/DVDISO/")) return launch_iso_game_mamba(path, EMU_DVD);

    if(use_mamba || mtype == EMU_BD || mtype == EMU_PSX)
    {
        return launch_iso_game_mamba(path, mtype);
    }

mount_iso: ;
    int is_ps2_game = 0;

    uint8_t *plugin_args = malloc(0x20000);

    if(plugin_args)
    {
        struct stat s;

        sprintf((char *) plugin_args, PLUGIN_ISO, self_path);

        if(stat((char *) plugin_args, &s) != SUCCESS) {free(plugin_args); return FAILED;}

        if(mtype >= 0)
        {
            type = mtype;
            is_ps2_game = (type == EMU_PS2_DVD);
        }
        else if(strstr(path, "/PS3ISO"))  type = EMU_PS3;
        else if(strstr(path, "/PS2ISO")) {type = EMU_PS2_DVD; is_ps2_game = 1;}
        else if(strstr(path, "/PSPISO"))  type = EMU_PSP;
        else if(strstr(path, "/PSXISO"))  type = EMU_PSX;
        else if(strstr(path, "/DVDISO"))  type = EMU_DVD;
        else if(strstr(path, "/BDISO"))   type = EMU_BD;
        else
        {
            FILE *fp = NULL;

            if(stat(path, &s) == SUCCESS) fp = fopen(path, "rb");

            if(fp)
            {
                fseek(fp, 0x8000, SEEK_SET);
                fread((void *) plugin_args, 1, 256, fp);

                fseek(fp, 0x9320, SEEK_SET);
                fread((void *) plugin_args + 256, 1, 256, fp);

                fclose(fp);

                if(!memcmp((void *) &plugin_args[8], "PSP GAME", 8)) type = EMU_PSP;
                else if(!memcmp((void *) &plugin_args[1], "BEA01", 5)) type = EMU_BD;
                else if(!memcmp((void *) &plugin_args[0x28], "PS3VOLUME", 9)) type = EMU_PS3;
                else if(!memcmp((void *) &plugin_args[8], "PLAYSTATION", 11) || !memcmp((void *) &plugin_args[256], "PLAYSTATION", 11) )
                {
                    if(is_ntfs_path(path))
                        type = EMU_PSX;
                    else
                    {
                        type = EMU_PS2_DVD; is_ps2_game = 1;
                    }
                }
            }
        }

        if(is_ntfs_path(path))
        {
            uint32_t *sections = malloc(MAX_SECTIONS * sizeof(uint32_t));
            uint32_t *sections_size = malloc(MAX_SECTIONS * sizeof(uint32_t));

            if(plugin_args && sections && sections_size && (type == EMU_PS3 || type == EMU_DVD || type == EMU_BD || type == EMU_PSX))
            {
                rawseciso_args *p_args;

                memset(sections, 0, MAX_SECTIONS * sizeof(uint32_t));
                memset(sections_size, 0, MAX_SECTIONS * sizeof(uint32_t));

                memset(plugin_args, 0, 0x10000);

                int parts = ps3ntfs_file_to_sectors(path, sections, sections_size, MAX_SECTIONS, 1);

                if(!strcmpext(path, ".iso.0"))
                {
                    sprintf(TEMP_PATH2, "%s", path);
                    temp_buffer[TEMP_PATH2_OFFSET + strlen(TEMP_PATH2) - 1] = 0;

                    for (int o = 1; o < 64; o++)
                    {
                        if(parts >= MAX_SECTIONS) break;

                        sprintf(TEMP_PATH1, "%s%i", TEMP_PATH2, o);
                        if(file_exists(TEMP_PATH1) == false) break;

                        parts += ps3ntfs_file_to_sectors(TEMP_PATH1, sections + parts, sections_size + parts, MAX_SECTIONS - parts, 1);
                    }
                }

                if(parts>0 && parts < MAX_SECTIONS)
                {
                    p_args = (rawseciso_args *)plugin_args;
                    p_args->device = USB_MASS_STORAGE(NTFS_Test_Device(&path[1]));
                    p_args->emu_mode = type;
                    p_args->num_sections = parts;
                    p_args->num_tracks = 0;


                    memcpy(plugin_args + sizeof(rawseciso_args), sections, parts * sizeof(uint32_t));
                    memcpy(plugin_args + sizeof(rawseciso_args) + (parts * sizeof(uint32_t)), sections_size, parts * sizeof(uint32_t));

                    cobra_unload_vsh_plugin(0);

                    sprintf(TEMP_PATH, PLUGIN_ISO, self_path);

                    int r = cobra_load_vsh_plugin(0, TEMP_PATH, plugin_args, 0x10000);
                    if (r == 0) {fun_exit(); SaveGameList(); exit(0);}

                    sprintf(MEM_MESSAGE, "error %X loading sprx_iso plugin", r);
                    DrawDialogOK(MEM_MESSAGE);

                }
                else
                {
                    if(parts >= MAX_SECTIONS) DrawDialogOKTimer(".ISO is very fragmented", 2000.0f);
                }

                if(plugin_args) free(plugin_args); plugin_args = NULL;
                if(sections) free(sections);
                if(sections_size) free(sections_size);
            }

        }
        else if((type == EMU_PS3 || type == EMU_DVD || type == EMU_BD || type == EMU_PSX) ||
                (type == EMU_PS2_DVD && strncmp(path, "/dev_usb", 8)))
        {
            if(plugin_args) free(plugin_args); plugin_args = NULL;

            if(is_ps2_game) unlink_secure("/dev_hdd0/classic_ps2");

            if (!use_cobra && use_mamba)
            {
                if(is_ps2_game) return FAILED;
                else goto mount_with_mamba;
            }

            int ret = FAILED;

            char *files[32];
            int nfiles = 1;

            files[0] = path;
            files[1] = NULL;

            if(!strcmpext(path, ".iso.0"))
            {
                sprintf(TEMP_PATH2, "%s", path);
                temp_buffer[TEMP_PATH2_OFFSET + strlen(TEMP_PATH2) - 1] = 0;

                for (int o = 1; o < 64; o++)
                {
                    files[o] = malloc(1024);
                    if(!files[o]) break;

                    sprintf(files[o], "%s%i", TEMP_PATH2, o);
                    if(file_exists(files[o]) == false) break;

                    nfiles++;
                }
            }

            if(type == EMU_PS3)
                ret = cobra_mount_ps3_disc_image(files, nfiles);
            else if(type == EMU_PS2_DVD)
                ret = cobra_mount_ps2_disc_image(files, nfiles, (TrackDef *) TEMP_PATH1, 1);
            else if(type == EMU_PSX)
                ret = cobra_mount_psx_disc_image(path, (TrackDef *) TEMP_PATH1, 1);
            else if(type == EMU_PSP)
                ret = mount_psp_iso(path);
            else if(type == EMU_DVD)
                ret = cobra_mount_dvd_disc_image(files, nfiles);
            else if(type == EMU_BD)
                ret = cobra_mount_bd_disc_image(files, nfiles);
            else ret = FAILED;

            if (ret == SUCCESS)
            {
                cobra_send_fake_disc_insert_event();
                {fun_exit(); SaveGameList(); exit(0);}
            }

            for(int o = 1; o < 64; o++) if(files[o]) free(files[o]);
        }
        else
mount_with_mamba:
        {
            char *sections = malloc(64 * 0x200);
            uint32_t *sections_size = malloc(64 * sizeof(uint32_t));

            if(plugin_args && sections && sections_size)
            {
                rawseciso_args *p_args;

                memset(sections, 0, 64 * 0x200);
                memset(sections_size, 0, 64 * sizeof(uint32_t));

                memset(plugin_args, 0, 0x10000);

                int parts = 0;

                if(!strcmpext(path, ".iso.0"))
                {
                    for(int o = 0; o < 64; o++)
                    {
                        struct stat s;

                        sprintf(TEMP_PATH2, "%s", path);
                        temp_buffer[TEMP_PATH2_OFFSET + strlen(TEMP_PATH2) - 1] = 0;

                        sprintf(&sections[0x200 * o], "%s%i", TEMP_PATH2, o);

                        if(stat(&sections[0x200 * o], &s) != SUCCESS) {memset(&sections[0x200 * o], 0, 0x200); break;}
                        sections_size[o] = s.st_size / 2048ULL;

                        parts++;
                    }
                }
                else
                {
                    parts = 1;

                    strncpy(&sections[0], path, 0x1ff);
                    sections[0x1ff] = 0;

                    if(stat(&sections[0], &s) != SUCCESS) goto skip_load;
                    sections_size[0] = s.st_size / 2048ULL;
                }

                p_args = (rawseciso_args *)plugin_args;
                p_args->device = USB_MASS_STORAGE(NTFS_Test_Device(&path[1]));
                p_args->emu_mode = type | 1024;
                p_args->num_sections = parts;
                p_args->num_tracks = 0;

                memcpy(plugin_args + sizeof(rawseciso_args), sections, parts * 0x200);
                memcpy(plugin_args + sizeof(rawseciso_args) + (parts * 0x200), sections_size, parts * sizeof(uint32_t));

                cobra_unload_vsh_plugin(0);

                sprintf(TEMP_PATH1, PLUGIN_ISO, self_path);
                int r = cobra_load_vsh_plugin(0, TEMP_PATH1, plugin_args, 0x10000);
                if (r == 0) {fun_exit(); SaveGameList(); exit(0);}

                sprintf(MEM_MESSAGE, "error %X loading sprx_iso plugin", r);
                DrawDialogOK(MEM_MESSAGE);
            }


 skip_load:
            if(plugin_args) free(plugin_args); plugin_args = NULL;
            if(sections) free(sections);
            if(sections_size) free(sections_size);
        }
    }

    if(plugin_args) free(plugin_args); plugin_args = NULL;

    return FAILED;

}

int launch_iso_game_mamba(char *path, int mtype)
{
    int type = EMU_DVD;

    int is_ps2_game = 0;

    uint8_t *plugin_args = malloc(0x20000);

    if(plugin_args)
    {
        struct stat s;

        sprintf((char *) plugin_args, PLUGIN_ISO, self_path);

        if(stat((char *) plugin_args, &s) != SUCCESS) {free(plugin_args); return FAILED;}

        if(mtype >= 0)
        {
            type = mtype;
            is_ps2_game = (type == EMU_PS2_DVD);
        }
        else if(strstr(path, "/PS3ISO"))  type = EMU_PS3;
        else if(strstr(path, "/PS2ISO")) {type = EMU_PS2_DVD; is_ps2_game = 1;}
        else if(strstr(path, "/PSPISO"))  type = EMU_PSP;
        else if(strstr(path, "/PSXISO"))  type = EMU_PSX;
        else if(strstr(path, "/DVDISO"))  type = EMU_DVD;
        else if(strstr(path, "/BDISO"))   type = EMU_BD;
        else
        {
            FILE *fp = NULL;

            if(stat(path, &s) == SUCCESS) fp = fopen(path, "rb");

            if(fp)
            {
                fseek(fp, 0x8000, SEEK_SET);
                fread((void *) plugin_args, 1, 256, fp);

                fseek(fp, 0x9320, SEEK_SET);
                fread((void *) plugin_args + 256, 1, 256, fp);

                fclose(fp);

                if(!memcmp((void *) &plugin_args[8], "PSP GAME", 8)) type = EMU_PSP;
                else if(!memcmp((void *) &plugin_args[1], "BEA01", 5)) type = EMU_BD;
                else if(!memcmp((void *) &plugin_args[0x28], "PS3VOLUME", 9)) type = EMU_PS3;
                else if(!memcmp((void *) &plugin_args[8], "PLAYSTATION", 11) || !memcmp((void *) &plugin_args[256], "PLAYSTATION", 11) )
                {
                    if(is_ntfs_path(path))
                        type = EMU_PSX;
                    else
                    {
                        type = EMU_PS2_DVD; is_ps2_game = 1;
                    }
                }
            }
        }

        if(is_ntfs_path(path))
        {
            uint32_t *sections = malloc(MAX_SECTIONS * sizeof(uint32_t));
            uint32_t *sections_size = malloc(MAX_SECTIONS * sizeof(uint32_t));

            if(plugin_args && sections && sections_size && (type == EMU_PS3 || type == EMU_DVD || type == EMU_BD || type == EMU_PSX))
            {
                rawseciso_args *p_args;

                memset(sections, 0, MAX_SECTIONS * sizeof(uint32_t));
                memset(sections_size, 0, MAX_SECTIONS * sizeof(uint32_t));

                memset(plugin_args, 0, 0x10000);

                int parts = ps3ntfs_file_to_sectors(path, sections, sections_size, MAX_SECTIONS, 1);

                if(!strcmpext(path, ".iso.0"))
                {
                    sprintf(TEMP_PATH2, "%s", path);
                    temp_buffer[TEMP_PATH2_OFFSET + strlen(TEMP_PATH2) - 1] = 0;

                    for (int o = 1; o < 64; o++)
                    {
                        if(parts >= MAX_SECTIONS) break;

                        sprintf(TEMP_PATH1, "%s%i", TEMP_PATH2, o);
                        if(file_exists(TEMP_PATH1) == false) break;

                        parts += ps3ntfs_file_to_sectors(TEMP_PATH1, sections + parts, sections_size + parts, MAX_SECTIONS - parts, 1);
                    }
                }

                if(parts>0 && parts < MAX_SECTIONS)
                {
                    p_args = (rawseciso_args *)plugin_args;
                    p_args->device = USB_MASS_STORAGE(NTFS_Test_Device(&path[1]));
                    p_args->emu_mode = type;
                    p_args->num_sections = parts;
                    p_args->num_tracks = 0;

                    memcpy(plugin_args + sizeof(rawseciso_args), sections, parts * sizeof(uint32_t));
                    memcpy(plugin_args + sizeof(rawseciso_args) + (parts * sizeof(uint32_t)), sections_size, parts * sizeof(uint32_t));

                    cobra_unload_vsh_plugin(0);

                    sprintf(TEMP_PATH1, PLUGIN_ISO, self_path);

                    if (cobra_load_vsh_plugin(0, TEMP_PATH1, plugin_args, 0x10000) == 0) {fun_exit(); SaveGameList(); exit(0);}
                }
                else if(parts >= MAX_SECTIONS) DrawDialogOKTimer(".ISO is very fragmented", 2000.0f);

                if(plugin_args) free(plugin_args); plugin_args = NULL;
                if(sections) free(sections);
                if(sections_size) free(sections_size);
            }
        }
        else if(type == EMU_PS3 || (type == EMU_PS2_DVD && strncmp(path, "/dev_usb", 8))
             || type == EMU_DVD || type == EMU_BD)
        {
            if(is_ps2_game)
            {
                unlink_secure("/dev_hdd0/classic_ps2");

                if(plugin_args) free(plugin_args); plugin_args = NULL;

                if(use_mamba) return FAILED;

                int ret;

                char *files[32];
                int nfiles = 1;

                files[0] = path;
                files[1] = NULL;

                if(!strcmpext(path, ".iso.0"))
                {
                    sprintf(TEMP_PATH2, "%s", path);
                    temp_buffer[TEMP_PATH2_OFFSET + strlen(TEMP_PATH2) - 1] = 0;

                    for (int o = 1; o < 64; o++)
                    {
                        files[o] = malloc(1024);
                        if(!files[o]) break;

                        sprintf(files[o], "%s%i", TEMP_PATH2, o);
                        if(file_exists(files[o]) == false) break;

                        nfiles++;
                    }
                }

                if(type == EMU_PS3)
                    ret = cobra_mount_ps3_disc_image(files, nfiles);
                else if(type == EMU_PS2_DVD)
                    ret = cobra_mount_ps2_disc_image(files, nfiles, (TrackDef *) TEMP_PATH1, 1);
                else if(type == EMU_PSX)
                    ret = cobra_mount_psx_disc_image(path, (TrackDef *) TEMP_PATH1, 1);
                else if(type == EMU_PSP)
                    ret = mount_psp_iso(path);
                else if(type == EMU_DVD)
                    ret = cobra_mount_dvd_disc_image(files, nfiles);
                else if(type == EMU_BD)
                    ret = cobra_mount_bd_disc_image(files, nfiles);
                else ret = FAILED;

                if (ret == SUCCESS)
                {
                    cobra_send_fake_disc_insert_event();
                    {fun_exit(); SaveGameList(); exit(0);}
                }

                for(int o = 1; o < 64; o++) if(files[o]) free(files[o]);
            }
            else
            {
                char *sections = malloc(64 * 0x200);
                uint32_t *sections_size = malloc(64 * sizeof(uint32_t));

                if(plugin_args && sections && sections_size)
                {
                    rawseciso_args *p_args;

                    memset(sections, 0, 64 * 0x200);
                    memset(sections_size, 0, 64 * sizeof(uint32_t));

                    memset(plugin_args, 0, 0x10000);

                    int parts = 0;

                    if(!strcmpext(path, ".iso.0"))
                    {
                        for(int o = 0; o < 64; o++)
                        {
                            struct stat s;

                            sprintf(TEMP_PATH2, "%s", path);
                            temp_buffer[TEMP_PATH2_OFFSET + strlen(TEMP_PATH2) - 1] = 0;

                            sprintf(&sections[0x200 * o], "%s%i", TEMP_PATH2, o);

                            if(stat(&sections[0x200 * o], &s) != SUCCESS) {memset(&sections[0x200 * o], 0, 0x200); break;}
                            sections_size[o] = s.st_size / 2048ULL;

                            parts++;
                        }
                    }
                    else
                    {
                        parts = 1;

                        strncpy(&sections[0], path, 0x1ff);
                        sections[0x1ff] = 0;

                        if(stat(&sections[0], &s) != SUCCESS) goto skip_load;
                        sections_size[0] = s.st_size / 2048ULL;
                    }

                    p_args = (rawseciso_args *)plugin_args;
                    p_args->device = USB_MASS_STORAGE(NTFS_Test_Device(&path[1]));
                    p_args->emu_mode = type | 1024;
                    p_args->num_sections = parts;
                    p_args->num_tracks = 0;


                    memcpy(plugin_args + sizeof(rawseciso_args), sections, parts * 0x200);
                    memcpy(plugin_args + sizeof(rawseciso_args) + (parts * 0x200), sections_size, parts * sizeof(uint32_t));

                    cobra_unload_vsh_plugin(0);

                    sprintf(TEMP_PATH1, PLUGIN_ISO, self_path);
                    int r = 0;
                    if ((r = cobra_load_vsh_plugin(0, TEMP_PATH1, plugin_args, 0x10000)) == 0) {fun_exit(); SaveGameList(); exit(0);}

                    sprintf(MEM_MESSAGE, "error %X", r);
                    DrawDialogOK(MEM_MESSAGE);
                }


            skip_load:

                if(plugin_args) free(plugin_args); plugin_args = NULL;
                if(sections) free(sections);
                if(sections_size) free(sections_size);
            }

        }
    }

    if(plugin_args) free(plugin_args); plugin_args = NULL;

    return FAILED;
}

int launch_iso_build(char *iso_path, char *src_path, bool run_showtime)
{
    int type = EMU_DVD; bool is_ntfs_file = strstr(iso_path, "/dev_hdd0/tmp/wmtmp");

    if(run_showtime && is_audiovideo(get_extension(src_path))) launch_video(src_path);

    if(is_audiovideo(get_extension(src_path)) || strstr(src_path, ".pkg") || is_ntfs_file)
    {
        if(run_showtime) launch_video(src_path);

        //ntfs
        type = EMU_BD;
    }

    sprintf(TEMP_PATH, "%s/USRDIR/TEMP", self_path);
    mkdir_secure(TEMP_PATH);

    if(use_cobra)
    {
        cobra_umount_disc_image();
        usleep(4000);
        cobra_send_fake_disc_eject_event();
    }

    uint8_t *plugin_args = malloc(0x20000);

    if(plugin_args)
    {
        sprintf((char*)plugin_args, PLUGIN_ISO, self_path);

        if(file_exists((char*)plugin_args) == false) {free(plugin_args); DrawDialogOK("ERROR: ISO Plugin not found"); return FAILED;}

        if(file_exists(src_path) == false) {sprintf(MEM_MESSAGE, "ERROR: %s could not be found", src_path); DrawDialogOK(MEM_MESSAGE); return FAILED;}

        u64 size;
        size = get_filesize(src_path);

        char filename[MAXPATHLEN]; //name only
        sprintf(filename, "%s", get_filename(src_path));;
        create_fake_file_iso(iso_path, filename, size);

        if(file_exists(iso_path) == false) {sprintf(MEM_MESSAGE, "ERROR: %s could not be found", iso_path); DrawDialogOK(MEM_MESSAGE); return FAILED;}

        int r = FAILED;

        if(is_ntfs_path(src_path))
        {
            uint32_t *sections      = malloc(MAX_SECTIONS * sizeof(uint32_t));
            uint32_t *sections_size = malloc(MAX_SECTIONS * sizeof(uint32_t));

            if(plugin_args && sections && sections_size)
            {
                rawseciso_args *p_args;

                memset(sections, 0, MAX_SECTIONS * sizeof(uint32_t));
                memset(sections_size, 0, MAX_SECTIONS * sizeof(uint32_t));

                memset(plugin_args, 0, 0x10000);

                // create file section
                strncpy((char *) sections, iso_path, 0x1ff);
                ((char *) sections)[0x1ff] = 0;

                size = get_filesize(iso_path);
                if (size == 0) goto skip_load_ntfs;
                sections_size[0] = size / 2048ULL;
                sections[0x200/4] = 0;
                int parts = 1;

                if(parts < MAX_SECTIONS)
                    parts += ps3ntfs_file_to_sectors(src_path, sections + parts + 0x200/4, sections_size + parts, MAX_SECTIONS - parts - 0x200/4, 1);

                if (parts > 0 && parts < (MAX_SECTIONS - 0x200/4))
                {
                    p_args = (rawseciso_args *)plugin_args;
                    p_args->device = USB_MASS_STORAGE(NTFS_Test_Device(&src_path[1]));
                    p_args->emu_mode = type | 0x800;
                    p_args->num_sections = parts;
                    p_args->num_tracks = 0;


                    memcpy(plugin_args + sizeof(rawseciso_args), sections, parts * sizeof(uint32_t) + 0x200);
                    memcpy(plugin_args + sizeof(rawseciso_args) + (parts*sizeof(uint32_t) + 0x200), sections_size, parts * sizeof(uint32_t));

                    if(is_ntfs_file)
                    {
                        // save sectors file
                        iso_path[strlen(iso_path)-4]=0; strcat(iso_path, ".ntfs[BDFILE]");

                        int fd = ps3ntfs_open(iso_path, O_WRONLY | O_CREAT | O_TRUNC, 0777);
                        if(fd >= 0)
                        {
                            if(ps3ntfs_write(fd, (void *) plugin_args, 0x10000)==0x10000) r = SUCCESS;
                            ps3ntfs_close(fd);
                        }
                    }
                    else
                    {
                        cobra_unload_vsh_plugin(0);
                        sprintf(TEMP_PATH, PLUGIN_ISO, self_path);
                        r = cobra_load_vsh_plugin(0, TEMP_PATH, plugin_args, 0x10000);
                    }
                }
                else
                {
                    if(parts >= (MAX_SECTIONS - 0x200/4)) DrawDialogOKTimer(".ISO is very fragmented", 2000.0f);
                }
           skip_load_ntfs:
                if(sections) free(sections);
                if(sections_size) free(sections_size);
            }
        }
        else
        {
            char *sections = malloc(64 * 0x200);
            uint32_t *sections_size = malloc(64 * sizeof(uint32_t));

            if(plugin_args && sections && sections_size)
            {
                rawseciso_args *p_args;

                memset(sections, 0, 64 * 0x200);
                memset(sections_size, 0, 64 * sizeof(uint32_t));

                memset(plugin_args, 0, 0x10000);

                int parts = 2;

                strncpy(&sections[0], iso_path, 0x1ff);
                sections[0x1ff] = 0;

                size = get_filesize(iso_path);
                if (size == 0) goto skip_load;
                sections_size[0] = size / 2048ULL;

                if(file_exists(src_path) == false) goto skip_load;
                strncpy(&sections[0x200], src_path, 0x1ff);
                sections[0x1ff] = 0;
                sections_size[1] = (size + 2047ULL) / 2048ULL;

                p_args = (rawseciso_args *)plugin_args;
                p_args->device = USB_MASS_STORAGE(NTFS_Test_Device(&iso_path[1]));
                p_args->emu_mode = type | 1024;
                p_args->num_sections = parts;
                p_args->num_tracks = 0;

                memcpy(plugin_args + sizeof(rawseciso_args), sections, parts * 0x200);
                memcpy(plugin_args + sizeof(rawseciso_args) + (parts * 0x200), sections_size, parts * sizeof(uint32_t));

                if(is_ntfs_file)
                {
                    // save sectors file
                    iso_path[strlen(iso_path)-4]=0; strcat(iso_path, ".ntfs[BDFILE]");

                    int fd = ps3ntfs_open(iso_path, O_WRONLY | O_CREAT | O_TRUNC, 0777);
                    if(fd >= 0)
                    {
                        if(ps3ntfs_write(fd, (void *) plugin_args, 0x10000)==0x10000) r = SUCCESS;
                        ps3ntfs_close(fd);
                    }
                }
                else
                {
                    cobra_unload_vsh_plugin(0);
                    sprintf(TEMP_PATH, PLUGIN_ISO, self_path);
                    r = cobra_load_vsh_plugin(0, TEMP_PATH, plugin_args, 0x10000);
                }
            }

    skip_load:
            if(sections) free(sections);
            if(sections_size) free(sections_size);
        }

        if(plugin_args) free(plugin_args); plugin_args = NULL;

        if(r == SUCCESS)
        {
            char name[65];
            strncpy(name, filename, 64);
            name[64] = 0;

            if(strlen(src_path) > 64)
            {
                // break the string
                int pos = 63 - strlen(get_extension(filename));
                while(pos > 0 && (name[pos] & 192) == 128) pos--; // skip UTF extra codes
                strcpy(&name[pos], get_extension(filename));
            }

            if(run_showtime) {sprintf(TEMP_PATH, "/dev_bdvd/%s", name); launch_video(TEMP_PATH);}
        }

        if(r==0) return SUCCESS;

        sprintf(MEM_MESSAGE, "error %X loading sprx_iso plugin", r);
        DrawDialogOK(MEM_MESSAGE);

    }
    else
        DrawDialogOK("ERROR: allocating 128KB memory");


    return FAILED;
}

static char help1[] = {
    "HELP - [ File Manager ]\n"
    "\n"
    "SELECT + START - Exit\n"
    "CROSS - Action for files/folders (Opens Hex Editor if selected)\n"
    "\n"
    "TRIANGLE - Opens menu selector (from the device)\n"
    "SQUARE - Single item selection\n"
    "SELECT + SQUARE - Select/Deselect all files/folders\n"
    "\n"
    "UP/DOWN - Move the cursor\n"
    "L1/R1 - Move the cursor by page\n"
    "LEFT/RIGHT - Switch window.\n"
    "SELECT+LEFT/RIGHT - Open current directory in the other window\n"
    "\n"
    "L2+R2 - Switch the window split mode (Vertical/Horizontal)\n"
    "L3/R3 - Changes to different frequently used paths\n"
};
#endif

#ifdef LOADER_MODE
void draw_file_manager() {}
int file_manager(char *pathw1, char *pathw2) {return 0;}
#else
static char cur_path1[MAX_PATH_LEN];
static char cur_path2[MAX_PATH_LEN];

void draw_file_manager()
{
        tiny3d_Flip();
        ps3pad_read();

        tiny3d_Project2D();
        cls2();
        update_twat(false);

        //// Begin drawing File Manager screen ////

        tiny3d_SetMatrixModelView(is_vsplit ? &mat_win1 : &mat_unit);
        DrawBox(0, 0, 0, 816, is_vsplit ? 48 : 32, BLUE5);
        DrawBox(816, 0, 0, 32, is_vsplit ? 48 : 32, (!fm_pane && (frame & BLINK_SLOW)) ? YELLOW : BLACK);
        set_ttf_window(8, 0, is_vsplit ? 590 : 592, is_vsplit ? 48 : 32, WIN_AUTO_LF);
        display_ttf_string(0, 0, (char *) path1, WHITE, 0, is_vsplit ? 16 : 12, 24);

        set_ttf_window(600, 0, 200, 32, WIN_AUTO_LF);
        if(free_device1 < 0x40000000LL)
            sprintf(temp_buffer, "%1.1f MB FREE", ((double) free_device1) / 0x100000LL);
        else
            sprintf(temp_buffer, "%1.2f GB FREE", ((double) free_device1) / GIGABYTES);

        if(free_device1 < GIGABYTES && strncmp(path1, "/dev_hdd0", 9) == SUCCESS)
            display_ttf_string(0, 0, (char *) temp_buffer, (frame & BLINK_SLOW) ? RED1 : GRAY, 0, 24, 32);
        else
            display_ttf_string(0, 0, (char *) temp_buffer, GRAY, 0, 24, 32);

        if(is_vsplit)
        {
            set_ttf_window(600, 29, 200, 24, WIN_AUTO_LF);
            if(selcount1 <= 0)
                sprintf(temp_buffer, "%i Items", nentries1);
            else if(selsize1 < 0x100000LL)
                sprintf(temp_buffer, "%i of %i (%1.1f KB)", selcount1, nentries1, (double) (selsize1  / 1024LL));
            else if(selsize1 < 0x40000000LL)
                sprintf(temp_buffer, "%i of %i (%1.1f MB)", selcount1, nentries1, (double) (selsize1 / 0x100000LL));
            else
                sprintf(temp_buffer, "%i of %i (%1.2f GB)", selcount1, nentries1, ((double) selsize1) / GIGABYTES);

            display_ttf_string(0, 0, (char *) temp_buffer, GRAY, 0, 20, 24);
        }

        set_ttf_window(816, 0, 36, 32, WIN_AUTO_LF);
        display_ttf_string(4, 0, (char *) "A", RED1, 0, 32, 32);

        DrawBox2(0, is_vsplit ? 48 : 32, 0, 848, is_vsplit ? (512 - 48) * 3/2: 256 - 32 /*, 0x2080c0ff*/);

        if(is_vsplit)
        {
            DrawLineBox(0, 0, 0, 848, 48, 0x2000ffff);

            DrawLineBox(-1, 48, 0, 848, 24 * 24 + 16, 0x2000ffff);
        }

        tiny3d_SetMatrixModelView(is_vsplit ? &mat_win2 : &mat_unit);
        DrawBox(0, 256, 0, 816, is_vsplit ? 48 : 32, BLUE5);
        DrawBox(816, 256, 0, 32, is_vsplit ? 48 : 32, (fm_pane && (frame & BLINK_SLOW)) ? YELLOW : BLACK);
        set_ttf_window(8, 256, is_vsplit ? 590 : 592, is_vsplit ? 48 : 32, WIN_AUTO_LF);
        display_ttf_string(0, 0, (char *) path2, WHITE, 0, is_vsplit ? 16 : 12, 24);

        set_ttf_window(600, 256, 200, 32, WIN_AUTO_LF);

        if(free_device2 < 0x40000000LL)
            sprintf(temp_buffer, "%1.1f MB FREE", ((double) free_device2) / 0x100000LL);
        else
            sprintf(temp_buffer, "%1.2f GB FREE", ((double) free_device2) / GIGABYTES);

        if(free_device2 < GIGABYTES && strncmp(path2, "/dev_hdd0", 9) == SUCCESS)
            display_ttf_string(0, 0, (char *) temp_buffer, (frame & BLINK_SLOW) ? RED1 : GRAY, 0, 24, 32);
        else
            display_ttf_string(0, 0, (char *) temp_buffer, GRAY, 0, 24, 32);

        if(is_vsplit)
        {
            set_ttf_window(600, 285, 200, 24, WIN_AUTO_LF);
            if(selcount2 <= 0)
                sprintf(temp_buffer, "%i Items", nentries2);
            else if(selsize2 < 0x100000LL)
                sprintf(temp_buffer, "%i of %i (%1.1f KB)", selcount2, nentries2, (double) (selsize2  / 1024LL));
            else if(selsize2 < 0x40000000LL)
                sprintf(temp_buffer, "%i of %i (%1.1f MB)", selcount2, nentries2, (double) (selsize2 / 0x100000LL));
            else
                sprintf(temp_buffer, "%i of %i (%1.2f GB)", selcount2, nentries2, ((double) selsize2) / GIGABYTES);

            display_ttf_string(0, 0, (char *) temp_buffer, GRAY, 0, 20, 24);
        }

        set_ttf_window(816, 256, 36, 32, WIN_AUTO_LF);
        display_ttf_string(4, 0, (char *) "B", RED1, 0, 32, 32);

        DrawBox2(0, (is_vsplit ? 48 : 32) + 256 , 0, 848, is_vsplit? (512 - 48) * 3/2 : 256 - 32/*, 0x2080c0ff*/);

        if(is_vsplit)
        {
            DrawLineBox(0, 256, 0, 848, 48, 0x2000ffff);

            DrawLineBox(-1, 48 + 256, 0, 848, 24 * 24 + 16, 0x2000ffff);
        }

        tiny3d_SetMatrixModelView(is_vsplit ? &mat_win1 : &mat_unit);

        set_ttf_window(24, is_vsplit ? 48 : 32, 848-24, is_vsplit ? 656 - 48 : 256 - 32, 0);

        if(nentries1)
        {
            int py = 0;

            if(sel1 > nentries1) sel1 = nentries1 > 0 ? nentries1 - 1: 0;

            if((sel1 >= pos1) && (frame & BLINK) && !fm_pane)
                DrawBox(0, py + (is_vsplit ? 48 : 32) + 24 * (sel1 - pos1), 0, 848, 24, CURSORCOLOR);
            else
                DrawBox(0, py + (is_vsplit ? 48 : 32) + 24 * (sel1 - pos1), 0, 848, 24, INVISIBLE);

            for(int n = 0; n < (is_vsplit? 24 : 9); n++)
            {
                if(pos1 + n >= nentries1) break;

                u32 color = WHITE;

                stat1.st_size = entries1_size[pos1 + n];
                stat1.st_mode = entries1[pos1 + n].d_type;

                if(entries1[pos1 + n].d_type & IS_DIRECTORY)
                {
                    if(entries1[pos1 + n].d_type & IS_NOT_AVAILABLE) color = YELLOW;
                    else color = YELLOW2;
                    display_icon(0, py + (is_vsplit ? 50 : 34), 0, FILE_TYPE_FOLDER);
                }
                else
                {
                    int type = entries1_type[pos1 + n];

                    if(type < 1)
                    {
                        type = FILE_TYPE_NORMAL;
                        char *ext = get_extension(entries1[pos1 + n].d_name);
                        if(!strcasecmp(ext, ".pkg")) type = FILE_TYPE_PKG; else
                        if(!strcasecmp(ext, ".self")) type = FILE_TYPE_SELF; else
                        if(!strcasecmp(ext, ".png")) type = FILE_TYPE_PNG; else
                        if(!strcasecmp(ext, ".jpg")) type = FILE_TYPE_JPG; else
                        if(!strcasecmp(ext, ".zip")) type = FILE_TYPE_ZIP; else
                        if(!strcasecmp(ext, ".lua")) type = FILE_TYPE_LUA; else
                        if(strcasestr(".iso|.bin|.img|.mdf|.iso.0", ext) != NULL) type = FILE_TYPE_ISO; else
                        if(is_audiovideo(ext)) type = FILE_TYPE_ISO;

                        if(type == FILE_TYPE_ISO && strcmp(entries1[pos1 + n].d_name, "EBOOT.BIN") == SUCCESS)
                        {
                            color = CYAN;
                            entries1_type[pos1 + n] = FILE_TYPE_BIN;
                        }
                        else
                            entries1_type[pos1 + n] = type;
                    }
                    else if(type == FILE_TYPE_BIN)
                    {
                        color = CYAN;
                        type = FILE_TYPE_ISO;
                    }
                    if (type == FILE_TYPE_JPG) type = FILE_TYPE_PNG;

                    display_icon(0, py + (is_vsplit ? 50 : 34), 0, type);
                }

                if(entries1[pos1 + n].d_type & IS_MARKED)
                    DrawBox(0, py + (is_vsplit ? 52 : 36), 0, 848, 16, 0x800080a0);

                int dx = 0;

                double fsize = 0;

                if(/*sel1 == (pos1 + n) && */stat1.st_mode != 0xffffffff)
                {
                    if(stat1.st_mode == IS_DIRECTORY)
                    {
                        if((path1[1] == 0))
                        {
                            if(entries1_size[pos1 + n] > 0x10000) //if size > 64kb (1 cluster or more) use cached free space
                                fsize = (double) stat1.st_size;
                            else if(entries1[pos1 + n].d_name[0] == 'd' || entries1[pos1 + n].d_name[0] == 'n' || entries1[pos1 + n].d_name[0] == 'e') //dev_*, ntfs, ext
                            {
                                sprintf(TEMP_PATH, "/%s", entries1[pos1 + n].d_name);
                                fsize = (double) get_free_space(TEMP_PATH, true);
                                entries1_size[pos1 + n] = (s64) fsize;
                            }
                        }
                    }
                    else
                        fsize = (double) stat1.st_size;

                    if(stat1.st_mode == IS_DIRECTORY && fsize == 0)
                    { /* skip folders */}
                    else if(fsize < 1024LL)
                        sprintf(temp_buffer, "%1.0f B", fsize);
                    else if(fsize < 0x100000LL)
                        sprintf(temp_buffer, "%1.1f KB", fsize / 1024LL);
                    else if(fsize < 0x40000000LL)
                        sprintf(temp_buffer, "%1.1f MB", fsize / 0x100000LL);
                    else
                        sprintf(temp_buffer, "%1.2f GB", fsize / GIGABYTES);

                    dx = display_ttf_string(0, py, (char *) temp_buffer, 0, 0, is_vsplit ? 24 : 16, 24);
                }

                //set_ttf_window(24, is_vsplit ? 48 : 32, 848 - (dx + 24), 256 - 32, 0);
                set_ttf_window(24, is_vsplit ? 48 : 32, 848 - (dx + 24), is_vsplit ? 656 - 48 : 256 - 32, 0);

                int dxx = display_ttf_string(0, py, (char *) entries1[pos1 + n].d_name, color, 0, is_vsplit ? 24 : 16, 24);

                if((path1[1] == 0) && !strncmp( (char *) entries1[pos1 + n].d_name, "ntfs", 4))
                {
                    sprintf(MEM_MESSAGE, MSG_HOW_TO_UNMOUNT_DEVICE, NTFS_Test_Device((char *) entries1[pos1 + n].d_name));
                    display_ttf_string(dxx, py, MEM_MESSAGE, YELLOW, 0, is_vsplit ? 24 : 16, 24);
                }
                else
                if((path1[1] == 0) && !strncmp( (char *) entries1[pos1 + n].d_name, "ext", 3))
                {
                    sprintf(MEM_MESSAGE, MSG_HOW_TO_UNMOUNT_DEVICE, NTFS_Test_Device((char *) entries1[pos1 + n].d_name));
                    display_ttf_string(dxx, py, MEM_MESSAGE, YELLOW, 0, is_vsplit ? 24 : 16, 24);
                }

                if(stat1.st_mode == IS_DIRECTORY && fsize == 0)
                {
                    // don't show size for folders
                }
                else if(/*sel1 == (pos1 + n) && */stat1.st_mode != 0xffffffff)
                {
                    set_ttf_window(848 - dx, (is_vsplit ? 48 : 32), dx, is_vsplit ? 656 - 48 : 256 - 32, 0);
                    display_ttf_string(0, py, (char *) temp_buffer, 0xffffffff, 0, is_vsplit ? 24 : 16, 24);
                }

                py += 24;

            }
        }

        tiny3d_SetMatrixModelView(is_vsplit ? &mat_win2 : &mat_unit);

        set_ttf_window(24, (is_vsplit ? 48 : 32 ) + 256, 848 - 24, is_vsplit ? 656 - 48 : 256 - 32, 0);

        if(nentries2)
        {
            int py = 0;

            if(sel2 > nentries2) sel2 = nentries2 > 0 ? nentries2 - 1: 0;

            if((sel2 >= pos2) && (frame & BLINK) && fm_pane)
                DrawBox(0, py + (is_vsplit ? 48 : 32) + 256 + 24 * (sel2 - pos2), 0, 848, 24, CURSORCOLOR);
            else
                DrawBox(0, py + (is_vsplit ? 48 : 32) + 256 + 24 * (sel2 - pos2), 0, 848, 24, INVISIBLE);

            for(int n = 0; n < (is_vsplit? 24 : 9); n++)
            {
                if(pos2 + n >= nentries2) break;

                u32 color = WHITE;

                stat2.st_size = entries2_size[pos2 + n];
                stat2.st_mode = entries2[pos2 + n].d_type;

                if(entries2[pos2 + n].d_type & IS_DIRECTORY)
                {
                    if(entries2[pos2 + n].d_type & IS_NOT_AVAILABLE) color = YELLOW;
                    else color = YELLOW2;
                    display_icon(0, py + (is_vsplit ? 50 : 34) + 256 , 0, FILE_TYPE_FOLDER);
                }
                else
                {
                    int type = entries2_type[pos2 + n];

                    if(type < 1)
                    {
                        type = FILE_TYPE_NORMAL;
                        char *ext = get_extension(entries2[pos2 + n].d_name);
                        if(!strcasecmp(ext, ".pkg")) type = FILE_TYPE_PKG; else
                        if(!strcasecmp(ext, ".self")) type = FILE_TYPE_SELF; else
                        if(!strcasecmp(ext, ".png")) type = FILE_TYPE_PNG; else
                        if(!strcasecmp(ext, ".jpg")) type = FILE_TYPE_JPG; else
                        if(!strcasecmp(ext, ".zip")) type = FILE_TYPE_ZIP; else
                        if(!strcasecmp(ext, ".lua")) type = FILE_TYPE_LUA; else
                        if(strcasestr(".iso|.bin|.img|.mdf|.iso.0", ext) != NULL) type = FILE_TYPE_ISO; else
                        if(is_audiovideo(ext)) type = FILE_TYPE_ISO;

                        if(type == FILE_TYPE_ISO && strcmp(entries2[pos2 + n].d_name, "EBOOT.BIN") == SUCCESS)
                        {
                            color = CYAN;
                            entries2_type[pos2 + n] = FILE_TYPE_BIN;
                        }
                        else
                            entries2_type[pos2 + n] = type;
                    }
                    else if(type == FILE_TYPE_BIN)
                    {
                        color = CYAN;
                        type = FILE_TYPE_ISO;
                    }
                    if (type == FILE_TYPE_JPG) type = FILE_TYPE_PNG;

                    display_icon(0, py + (is_vsplit ? 50 : 34) + 256, 0, type);
                }

                if(entries2[pos2 + n].d_type & IS_MARKED)
                    DrawBox(0, py + (is_vsplit ? 52 : 36) + 256, 0, 848, 16, 0x800080a0);

                int dx = 0;

                double fsize = 0;

                if(/*sel2 == (pos2 + n) && */stat2.st_mode != 0xffffffff)
                {
                    if(stat2.st_mode == IS_DIRECTORY)
                    {
                        if((path2[1] == 0))
                        {
                            if(entries2_size[pos2 + n] > 0x10000) //if size > 64kb (1 cluster or more) use cached free space
                                fsize = (double) stat2.st_size;
                            else if(entries2[pos2 + n].d_name[0] == 'd' || entries2[pos2 + n].d_name[0] == 'n' || entries2[pos2 + n].d_name[0] == 'e') //dev_*, ntfs, ext
                            {
                                sprintf(TEMP_PATH, "/%s", entries2[pos2 + n].d_name);
                                fsize = (double) get_free_space(TEMP_PATH, true);
                                entries2_size[pos2 + n] = (s64) fsize;
                            }
                        }
                    }
                    else
                        fsize = (double) stat2.st_size;

                    if(stat2.st_mode == IS_DIRECTORY && fsize == 0)
                    { /* skip folders */}
                    else if(fsize < 1024LL)
                        sprintf(temp_buffer, "%1.0f B", fsize);
                    else if(fsize < 0x100000LL)
                        sprintf(temp_buffer, "%1.1f KB", fsize / 1024LL);
                    else if(fsize < 0x40000000LL)
                        sprintf(temp_buffer, "%1.1f MB", fsize / 0x100000LL);
                    else
                        sprintf(temp_buffer, "%1.2f GB", fsize / GIGABYTES);

                    dx = display_ttf_string(0, py, (char *) temp_buffer, 0, 0, is_vsplit ? 24 : 16, 24);
                }

                //set_ttf_window(24, 256 + 32, 848 - (dx + 24), 256 - 32, 0);
                set_ttf_window(24, (is_vsplit ? 48 : 32) + 256, 848 - (dx + 24), is_vsplit ? 656 - 48 : 256 - 32, 0);

                int dxx = display_ttf_string(0, py, (char *) entries2[pos2 + n].d_name, color, 0, is_vsplit ? 24 : 16, 24);

                if((path2[1] == 0) && !strncmp( (char *) entries2[pos2 + n].d_name, "ntfs", 4))
                {
                    sprintf(MEM_MESSAGE, MSG_HOW_TO_UNMOUNT_DEVICE, NTFS_Test_Device((char *) entries2[pos2 + n].d_name));
                    display_ttf_string(dxx, py, MEM_MESSAGE, YELLOW, 0, is_vsplit ? 24 : 16, 24);
                }
                else
                if((path2[1] == 0) && !strncmp( (char *) entries2[pos2 + n].d_name, "ext", 3))
                {
                    sprintf(MEM_MESSAGE, MSG_HOW_TO_UNMOUNT_DEVICE, NTFS_Test_Device((char *) entries2[pos2 + n].d_name));
                    display_ttf_string(dxx, py, MEM_MESSAGE, YELLOW, 0, is_vsplit ? 24 : 16, 24);
                }

                if(stat2.st_mode == IS_DIRECTORY && fsize == 0)
                {
                    // don't show size for folders
                }
                else if(/*sel2 == (pos2 + n) && */stat2.st_mode != 0xffffffff)
                {
                    set_ttf_window(848 - dx, (is_vsplit ? 48 : 32) + 256, dx, is_vsplit ? 656 - 48 : 256 - 32, 0);
                    display_ttf_string(0, py, (char *) temp_buffer, 0xffffffff, 0, is_vsplit ? 24 : 16, 24);
                }

                py += 24;

            }
        }

        tiny3d_SetMatrixModelView(&mat_unit);

        if(is_vsplit)
        {
            DrawBox(0, 512 - 32, 0, 848, 32, BLUE5);

            DrawLineBox(0, 512 - 32, 0, 848, 32, 0x2000ffff);

            set_ttf_window(848 - 312, 512 - 32, 480, 32, WIN_AUTO_LF);
            display_ttf_string(0, 0, (char *) "- File Manager", 0x208098cf, 0, 32, 32);
        }


        //// End drawing File Manager screen ////
}

int file_manager(char *pathw1, char *pathw2)
{
    static int auto_up = 0, auto_down = 0;

    update_devices1 = update_devices2 = false;

    frame = 300; //force immediate refresh

    int help = 0;
    int exitcode = 0;

    nentries1 = nentries2 = 0;

    free_device1 = 0ULL;
    free_device2 = 0ULL;

    bool dev_blind = false;

    bool is_ntfs = false;

    if(sysLv2FsStat("/dev_blind", &stat1)   == SUCCESS ||
       sysLv2FsStat("/dev_habib", &stat1)   == SUCCESS ||
       sysLv2FsStat("/dev_rewrite", &stat1) == SUCCESS) dev_blind = true;

    static int use_split = 1;
    static int counter_internal = 0;

    is_vsplit = Video_Resolution.width >= 1280 && use_split != 0;

    mat_unit = MatrixIdentity();
    mat_win1 = MatrixMultiply(MatrixTranslation(0.0f, 0.0f, 0.0f), MatrixScale(0.5f, 0.75f, 1.0f));
    mat_win2 = MatrixMultiply(MatrixTranslation(848.0f, -256.0f, 0.0f), MatrixScale(0.5f, 0.75f, 1.0f));

    int n, i;

    int img_width;
    int FullScreen = 0;
    int png_signal = 0;
    int tick1_move = 0;
    int tick2_move = 0;

    if(pathw1) strncpy(path1, pathw1, MAX_PATH_LEN);
    if(pathw2) strncpy(path2, pathw2, MAX_PATH_LEN);

    if(path1[0] == 0)
    {
        sprintf(TEMP_PATH, "%s/%s", self_path, "/config/path1.bin");
        if(file_exists(TEMP_PATH)) {n = MAX_PATH_LEN; char *buff = LoadFile(TEMP_PATH, &n); sprintf(path1, buff); if(buff) free(buff);}
    }
    if(path2[0] == 0)
    {
        sprintf(TEMP_PATH, "%s/%s", self_path, "/config/path2.bin");
        if(file_exists(TEMP_PATH)) {n = MAX_PATH_LEN; char *buff = LoadFile(TEMP_PATH, &n); sprintf(path2, buff); if(buff) free(buff);}
    }

    if(path1[0] == 0 || file_exists(path1) == false) strncpy(path1, "/", MAX_PATH_LEN);
    if(path2[0] == 0 || file_exists(path2) == false) strncpy(path2, "/", MAX_PATH_LEN);

    s32 fd;
    DIR_ITER *pdir = NULL;
    struct stat st;

    bool have_dot;

    stat1.st_mode = stat1.st_size = 0;
    stat2.st_mode = stat2.st_size = 0;

    update_device_sizes = 1|2; // force update both panes
    ntfs_mount_delay = 2;

    bool ft_update; u8 ft_count = 0;
    ft_update = ((path1[1] == 0) || (path2[1] == 0));

    free_device1 = get_free_space(path1, true);
    free_device2 = get_free_space(path2, true);

    draw_file_manager();

    while(true)
    {
        frame++;

        if(!nentries1) stat1.st_size = 0ULL;
        else
        {
            stat1.st_mode = (entries1[sel1].d_type & IS_DIRECTORY) ? IS_DIRECTORY : IS_FILE;
            stat1.st_size = entries1_size[sel1];
        }

        if(!nentries2) stat2.st_size = 0ULL;
        else
        {
            stat2.st_mode = (entries2[sel2].d_type & IS_DIRECTORY) ? IS_DIRECTORY : IS_FILE;
            stat2.st_size = entries2_size[sel2];
        }

        // NTFS Automount
        for(i = 0; i < 8; i++)
        {
            int r = NTFS_Event_Mount(i);

            if(r == 1)
            {   // mount device
                if(mounts[i])
                {   // change to root if unmount the device
                    frame = 600; //force immediate refresh
                    for (int k = 0; k < mountCount[i]; k++)
                    {
                        if((mounts[i]+k)->name[0])
                        {
                            if(!strncmp(&path1[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) {update_devices1 = true;}
                            if(!strncmp(&path2[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) {update_devices2 = true;}
                        }
                    }
                }

                NTFS_UnMount(i);

                mounts[i] = NULL;
                mountCount[i] = 0;
                mountCount[i] = ntfsMountDevice (disc_ntfs[i], &mounts[i], NTFS_DEFAULT | NTFS_RECOVER);
            }
            else if(r == -1)
            {   // unmount device
                if(mounts[i])
                {   // change to root if unmount the device
                    frame = 600; //force immediate refresh
                    for (int k = 0; k < mountCount[i]; k++)
                    {
                        if((mounts[i]+k)->name[0])
                        {
                            if(!strncmp(&path1[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) {update_devices1 = true;}
                            if(!strncmp(&path2[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) {update_devices2 = true;}
                        }
                    }

                    NTFS_UnMount(i);
                }
            }
        }

        if(update_devices1)
        {
            is_ntfs = is_ntfs_path(path1);

            if(!is_ntfs && sysLv2FsOpenDir(path1, &fd) == 0)
                sysLv2FsCloseDir(fd);
            else if(is_ntfs && (pdir = ps3ntfs_diropen(path1)) != NULL)
                ps3ntfs_dirclose(pdir);
            else
                path1[1] = 0; // to root

            nentries1 = pos1 = sel1 = 0;
            update_device_sizes |= 1;
        }

        if(update_devices2)
        {
            is_ntfs = is_ntfs_path(path2);

            if(!is_ntfs && sysLv2FsOpenDir(path2, &fd) == 0)
                sysLv2FsCloseDir(fd);
            else if(is_ntfs && (pdir = ps3ntfs_diropen(path2)) != NULL)
                ps3ntfs_dirclose(pdir);
            else
                path2[1] = 0; // to root

            nentries2 = pos2 = sel2 = 0;
            update_device_sizes |= 2;
        }

        if(ft_update)
        {
            ft_count++;
            if(ft_count > 1)
            {
                ft_update = false;
                if(path1[1] == 0) {nentries1 = pos1 = sel1 = 0; update_device_sizes |= 1; update_devices1 = true;}
                if(path2[1] == 0) {nentries2 = pos2 = sel2 = 0; update_device_sizes |= 2; update_devices2 = true;}
            }
            draw_file_manager();
        }
        // END NTFS Automount

        if (frame > 300 || nentries1 == 0 || nentries2 == 0 || update_devices1 || update_devices2)
        {
            frame = 0;

            // Update panel list #1

            if(update_devices1) {nentries1 = 0; update_device_sizes |= 1;}

            if((nentries1 == 0) || ((path1[1] == 0)))
            {
                have_dot = false;

                is_ntfs = is_ntfs_path(path1);

                if(nentries2 > 0 && update_devices1 == false && strcmp(path1, path2) == SUCCESS)
                {
                    memcpy(entries1, entries2, sizeof(entries2));
                    memcpy(entries1_type, entries2_type, sizeof(entries2_type));
                    memcpy(entries1_size, entries2_size, sizeof(entries2_size));

                    nentries1 = nentries2;
                    selcount1 = selsize1 = 0;

                    for(int i = 0; i < nentries1; i++)
                        entries1[i].d_type = (entries1[i].d_type & ~IS_MARKED);
                }
                else
                if((!is_ntfs && (sysLv2FsOpenDir(path1, &fd) == SUCCESS)) ||
                   ( is_ntfs && (pdir = ps3ntfs_diropen(path1)) != NULL))
                {
                    u64 read;

                    int old_entries = nentries1;
                    nentries1 = selcount1 = selsize1 = 0;

                    while((!is_ntfs && sysLv2FsReadDir(fd, &entries1[nentries1], &read) == 0 && read > 0) ||
                          ( is_ntfs && ps3ntfs_dirnext(pdir, entries1[nentries1].d_name, &st) == 0))
                    {
                        if(nentries1 >= MAX_ENTRIES) break;

                        if(entries1[nentries1].d_name[0] == '.')
                        {
                            if(entries1[nentries1].d_name[1] == 0) continue;
                            if(entries1[nentries1].d_name[1] == '.') have_dot = true;
                        }

                        if(is_ntfs)
                        {
                            entries1[nentries1].d_type = (S_ISDIR(st.st_mode)) ? IS_DIRECTORY : IS_FILE;
                        }

                        entries1_type[nentries1] = entries1_size[nentries1] = 0;

                        if(entries1[nentries1].d_type & IS_DIRECTORY)
                        {
                            entries1[nentries1].d_type = IS_DIRECTORY;
                            if((path1[1] == 0))
                            {
                                sysFSStat stat;
                                sprintf(temp_buffer, "%s/%s", path1, entries1[nentries1].d_name);
                                if(sysLv2FsStat(temp_buffer, &stat) != SUCCESS) entries1[nentries1].d_type |= IS_NOT_AVAILABLE;
                            }
                        }
                        else
                            entries1[nentries1].d_type = IS_FILE;

                        nentries1++;

                        tiny3d_Flip();
                        ps3pad_read();

                        if((old_pad & BUTTON_CIRCLE_) || (new_pad & BUTTON_CIRCLE_)) break;
                    }

                    if(is_ntfs) ps3ntfs_dirclose(pdir); else sysLv2FsCloseDir(fd);

                    if((path1[1] == 0))
                    {   // NTFS devices
                        int k;

                        for(k = 0; k < 8; k++)
                        {
                            for (i = 0; i < mountCount[k]; i++)
                            {
                                if(nentries1 >= MAX_ENTRIES) break;
                                if((mounts[k]+i)->name[0])
                                {
                                    entries1[nentries1].d_type = IS_DIRECTORY;
                                    sprintf(entries1[nentries1].d_name, "%s:", (mounts[k]+i)->name);
                                    entries1_type[nentries1] = 0;
                                    entries1_size[nentries1] = 0;
                                    nentries1++;
                                }
                            }
                        }
                    }

                    if((path1[1] != 0) && !have_dot)
                    {
                        entries1[nentries1].d_type = IS_DIRECTORY;
                        sprintf(entries1[nentries1].d_name, "..");
                        nentries1++;
                    }

                    if(old_entries > nentries1) pos1 = sel1 = 0;

                    qsort(entries1, nentries1, sizeof(sysFSDirent), entry_compare);
                    for (i = 0; i < nentries1; i++)
                    {
                        struct stat s;
                        if(path1[0] != 0)
                        {
                            sprintf(temp_buffer, "%s/%s", path1, entries1[i].d_name);
                            if(stat(temp_buffer, &s) == SUCCESS) entries1_size[i] = s.st_size;
                        }
                        else
                            entries1_size[i] = 0;
                    }
                    update_devices1 = false;
                }
            }


            // Update panel list #2

            if(update_devices2) {nentries2 = 0; update_device_sizes |= 2;}

            if((nentries2 == 0) || (path2[1] == 0))
            {

                have_dot = false;

                is_ntfs = is_ntfs_path(path2);

                if(nentries1 > 0 && update_devices2 == false && strcmp(path1, path2) == SUCCESS)
                {
                    memcpy(entries2, entries1, sizeof(entries1));
                    memcpy(entries2_type, entries1_type, sizeof(entries1_type));
                    memcpy(entries2_size, entries1_size, sizeof(entries1_size));

                    nentries2 = nentries1;
                    selcount2 = selsize2 = 0;

                    for(int i = 0; i < nentries2; i++)
                        entries2[i].d_type = (entries2[i].d_type & ~IS_MARKED);
                }
                else
                if((!is_ntfs && (sysLv2FsOpenDir(path2, &fd)) == SUCCESS) ||
                   ( is_ntfs && (pdir = ps3ntfs_diropen(path2)) != NULL))
                {
                    u64 read;

                    int old_entries = nentries2;
                    nentries2 = selcount2 = selsize2 = 0;

                    while((!is_ntfs && sysLv2FsReadDir(fd, &entries2[nentries2], &read) == 0 && read > 0) ||
                          ( is_ntfs && ps3ntfs_dirnext(pdir, entries2[nentries2].d_name, &st) == 0))
                    {
                        if(nentries2 >= MAX_ENTRIES) break;

                        if(entries2[nentries2].d_name[0] == '.')
                        {
                            if(entries2[nentries2].d_name[1] == 0) continue;
                            if(entries2[nentries2].d_name[1] == '.') have_dot = true;
                        }

                        if(is_ntfs)
                        {
                            entries2[nentries2].d_type = (S_ISDIR(st.st_mode)) ? IS_DIRECTORY : IS_FILE;
                        }

                        entries2_type[nentries2] = entries2_size[nentries2] = 0;

                        if(entries2[nentries2].d_type & IS_DIRECTORY)
                        {
                            entries2[nentries2].d_type = IS_DIRECTORY;
                            if((path2[1] == 0))
                            {
                                sysFSStat stat;
                                sprintf(temp_buffer, "%s/%s", path2, entries2[nentries2].d_name);
                                if(sysLv2FsStat(temp_buffer, &stat) != SUCCESS) entries2[nentries2].d_type |= IS_NOT_AVAILABLE;
                            }
                        }
                        else
                            entries2[nentries2].d_type = IS_FILE;

                        nentries2++;

                        tiny3d_Flip();
                        ps3pad_read();

                        if((old_pad & BUTTON_CIRCLE_) || (new_pad & BUTTON_CIRCLE_)) break;
                    }

                    if(is_ntfs) ps3ntfs_dirclose(pdir); else sysLv2FsCloseDir(fd);

                    if((path2[1] == 0))
                    {   // NTFS devices
                        int k;

                        for(k = 0; k < 8; k++)
                        {
                            for (i = 0; i < mountCount[k]; i++)
                            {
                                if(nentries2 >= MAX_ENTRIES) break;
                                if((mounts[k]+i)->name[0])
                                {
                                    entries2[nentries2].d_type = IS_DIRECTORY;
                                    sprintf(entries2[nentries2].d_name, "%s:", (mounts[k]+i)->name);
                                    entries2_type[nentries2] = 0;
                                    entries2_size[nentries2] = 0;
                                    nentries2++;
                                }
                            }
                        }
                    }

                    if((path2[1] != 0) && !have_dot)
                    {
                        entries2[nentries2].d_type = IS_DIRECTORY;
                        sprintf(entries2[nentries2].d_name, "..");
                        nentries2++;
                    }

                    if(old_entries > nentries2) pos2 = sel2 = 0;

                    qsort(entries2, nentries2, sizeof(sysFSDirent), entry_compare);
                    for (i = 0; i < nentries2; i++)
                    {
                        struct stat s;
                        if(path2[0] != 0)
                        {
                            sprintf(temp_buffer, "%s/%s", path2, entries2[i].d_name);
                            if(stat(temp_buffer, &s) == SUCCESS) entries2_size[i] = s.st_size;
                        }
                        else
                            entries2_size[i] = 0;
                    }
                    update_devices2 = false;
                }
            }
        }

        //-- hilight current path
        if(cur_path1[0] != 0 && nentries1)
        {
            sel1 = selcount1 = selsize1 = 0;

            for(int i = 0; i < nentries1 ; i++)
            {
                if(!strcmp(entries1[i].d_name, cur_path1))
                {
                    sel1 = i; pos1 = sel1;
                    if(is_vsplit)
                    {
                        if(sel1 >= 12) pos1 = sel1 - 12; else pos1 = 0;
                    }
                    else
                    {
                        if(sel1 >= 4) pos1 = sel1 - 4; else pos1 = 0;
                    }
                    break;
                }
            }

            cur_path1[0] = 0;
        }

        if(cur_path2[0] != 0 && nentries2)
        {
            sel2 = selcount2 = selsize2 = 0;

            for(int i = 0; i < nentries2 ; i++)
            {
                if(!strcmp(entries2[i].d_name, cur_path2))
                {
                    sel2 = i; pos2 = sel2;
                    if(is_vsplit)
                    {
                        if(sel2 >= 12) pos2 = sel2 - 12; else pos2 = 0;
                    }
                    else
                    {
                        if(sel2 >= 4) pos2 = sel2 - 4; else pos2 = 0;
                    }
                    break;
                }
            }

            cur_path2[0] = 0;
        }
        // ----


        counter_internal++;

        if(counter_internal >= 600)
        {
            counter_internal = 0;
            int r= ftp_net_status();

            if(r == -4) {
               ftp_net_deinit();
               ftp_net_init();
               r = ftp_net_status();
            }
        }


        // update free space (panel #1)

        if((update_device_sizes & 1) || (path1[1] == 0))
        {
            if(!nentries1) ;

            else if((path1[1] == 0))
            {
                sprintf(TEMP_PATH, "/%s", entries1[sel1].d_name);
                free_device1 = get_free_space(TEMP_PATH, true);
            }
            else
            {
                update_device_sizes &= ~1;
                free_device1 = get_free_space(path1, false);
            }

            if((path1[1] == 0))
                entries1_size[sel1] = free_device1;
            else if(strncmp(path1, path2, 11) == SUCCESS)
                {free_device2 = free_device1; update_device_sizes = 0;}
        }

        // update free space (panel #2)

        if((update_device_sizes & 2) || (path2[1] == 0))
        {
            if(!nentries2) ;

            else if((path2[1] == 0))
            {
                sprintf(TEMP_PATH, "/%s", entries2[sel2].d_name);
                free_device2 = get_free_space(TEMP_PATH, true);
                entries2_size[sel2] = free_device2;
            }
            else
            {
                update_device_sizes &= ~2;
                free_device2 = get_free_space(path2, false);
            }

            if((path1[1] == 0))
                entries1_size[sel1] = free_device1;
            else if(strncmp(path1, path2, 11) == SUCCESS)
                {free_device1 = free_device2; update_device_sizes = 0;}
        }

        draw_file_manager();

        // auto PNG
        if(tick1_move && (path1[1] != 0) && !fm_pane && png_signal < 110 && auto_up == 0 && auto_down == 0)
        {
            struct stat st;
            int signal = 0;

            if((entries1[sel1].d_type & IS_DIRECTORY) && (path1[12] == 'G' || path1[10] == 'G' || path1[10] == 'g' || path1[10] == 'h' || path1[5] == 'b'))
            {
                sprintf(temp_buffer, "%s/%s/PS3_GAME/ICON0.PNG", path1, entries1[sel1].d_name);
                if(!stat(temp_buffer, &st)) signal = 1;
                else
                {
                    sprintf(temp_buffer, "%s/%s/ICON0.PNG", path1, entries1[sel1].d_name);
                    if(!stat(temp_buffer, &st)) signal = 1;
                    else
                    {
                        sprintf(temp_buffer, "%s/../ICON0.PNG", path1);
                        if(!stat(temp_buffer, &st)) signal = 1;
                    }
                }

                tick1_move = 0;

                if((signal != 0) && LoadTexturePNG(temp_buffer, TEMP_PICT) == SUCCESS)
                {
                    png_signal = 120; FullScreen = 0;
                }
            }
            else if(!(entries1[sel1].d_type & IS_DIRECTORY))
            {
                tick1_move = 0;

                if(entries1_type[sel1] == FILE_TYPE_PNG)
                {
                    sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                    if(!stat(TEMP_PATH, &st)) signal = 1;

                    if(signal && LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if(entries1_type[sel1] == FILE_TYPE_JPG)
                {
                    sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                    if(!stat(TEMP_PATH, &st)) signal = 1;

                    if(signal && LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if (entries1_type[sel1] == FILE_TYPE_BIN)
                {
                    sprintf(TEMP_PATH, "%s/../ICON0.PNG", path1);
                    if(LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if(!strcmp(entries1[sel1].d_name, "PS3LOGO.DAT"))
                {
                    sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                    if(LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if(strlen(entries1[sel1].d_name) >= 40 && strstr(entries1[sel1].d_name, "_00-") != NULL)
                {
                    sprintf(TEMP_PATH, "/dev_hdd0/game/BLES80608/USRDIR/covers/%c%c%c%c%c%c%c%c%c.JPG",
                            entries1[sel1].d_name[ 7], entries1[sel1].d_name[ 8], entries1[sel1].d_name[ 9], entries1[sel1].d_name[10],
                            entries1[sel1].d_name[11], entries1[sel1].d_name[12], entries1[sel1].d_name[13], entries1[sel1].d_name[14], entries1[sel1].d_name[15]);

                    if(LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                    else
                    {
                        sprintf(TEMP_PATH, "/dev_hdd0/GAMES/covers/%c%c%c%c%c%c%c%c%c.JPG",
                                entries1[sel1].d_name[ 7], entries1[sel1].d_name[ 8], entries1[sel1].d_name[ 9], entries1[sel1].d_name[10],
                                entries1[sel1].d_name[11], entries1[sel1].d_name[12], entries1[sel1].d_name[13], entries1[sel1].d_name[14], entries1[sel1].d_name[15]);

                        if(LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 120; FullScreen = 0;
                        }
                    }
                }
                else
                {
                    tick1_move = 0;
                    sprintf(temp_buffer, "%s/%s", path1, entries1[sel1].d_name);

                    temp_buffer[strlen(temp_buffer) - 4] = 0;
                    strcat(temp_buffer, ".png");

                    if(file_exists(temp_buffer))
                    {
                        if(LoadTexturePNG(temp_buffer, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 120; FullScreen = 0;
                        }
                    }
                    else
                    {
                        temp_buffer[strlen(temp_buffer) - 4] = 0;
                        strcat(temp_buffer, ".jpg");

                        if(file_exists(temp_buffer))
                        {
                            if(LoadTextureJPG(temp_buffer, TEMP_PICT) == SUCCESS)
                            {
                                png_signal = 120; FullScreen = 0;
                            }
                        }
                    }
                }
            }
        }
        else if (tick2_move && (path2[1] != 0) && fm_pane && png_signal < 110 && auto_up == 0 && auto_down == 0)
        {
            struct stat st;
            int signal = 0;

            if((entries2[sel2].d_type & IS_DIRECTORY) && (path2[12] == 'G' || path2[10] == 'G' || path2[10] == 'g' || path2[10] == 'h' || path1[5] == 'b'))
            {
                sprintf(temp_buffer, "%s/%s/PS3_GAME/ICON0.PNG", path2, entries2[sel2].d_name);
                if(!stat(temp_buffer, &st)) signal = 1;
                else
                {
                    sprintf(temp_buffer, "%s/%s/ICON0.PNG", path2, entries2[sel2].d_name);
                    if(!stat(temp_buffer, &st)) signal = 1;
                    else
                    {
                        sprintf(temp_buffer, "%s/../ICON0.PNG", path2);
                        if(!stat(temp_buffer, &st)) signal = 1;
                    }
                }

                tick2_move = 0;

                if((signal != 0) && LoadTexturePNG(temp_buffer, TEMP_PICT) == SUCCESS)
                {
                    png_signal = 120; FullScreen = 0;
                }

            }
            else if(!(entries2[sel2].d_type & IS_DIRECTORY))
            {
                tick2_move = 0;

                if(entries2_type[sel2] == FILE_TYPE_PNG)
                {
                    sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                    if(!stat(TEMP_PATH, &st)) signal = 1;

                    if(signal && LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if(entries2_type[sel2] == FILE_TYPE_JPG)
                {
                    sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                    if(!stat(TEMP_PATH, &st)) signal = 1;

                    if(signal && LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if (entries2_type[sel2] == FILE_TYPE_BIN)
                {
                    sprintf(TEMP_PATH, "%s/../ICON0.PNG", path2);
                    if(LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if(!strcmp(entries2[sel2].d_name, "PS3LOGO.DAT"))
                {
                    sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                    if(LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                }
                else if(strlen(entries2[sel2].d_name) >= 40 && strstr(entries2[sel2].d_name, "_00-") != NULL)
                {
                    sprintf(TEMP_PATH, "/dev_hdd0/game/BLES80608/USRDIR/covers/%c%c%c%c%c%c%c%c%c.JPG",
                            entries2[sel2].d_name[ 7], entries2[sel2].d_name[ 8], entries2[sel2].d_name[ 9], entries2[sel2].d_name[10],
                            entries2[sel2].d_name[11], entries2[sel2].d_name[12], entries2[sel2].d_name[13], entries2[sel2].d_name[14], entries2[sel2].d_name[15]);

                    if(LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                    {
                        png_signal = 120; FullScreen = 0;
                    }
                    else
                    {
                        sprintf(TEMP_PATH, "/dev_hdd0/GAMES/covers/%c%c%c%c%c%c%c%c%c.JPG",
                                entries2[sel2].d_name[ 7], entries2[sel2].d_name[ 8], entries2[sel2].d_name[ 9], entries2[sel2].d_name[10],
                                entries2[sel2].d_name[11], entries2[sel2].d_name[12], entries2[sel2].d_name[13], entries2[sel2].d_name[14], entries2[sel2].d_name[15]);

                        if(LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 120; FullScreen = 0;
                        }
                    }
                }
                else
                {
                    tick2_move = 0;
                    sprintf(temp_buffer, "%s/%s", path2, entries2[sel2].d_name);

                    temp_buffer[strlen(temp_buffer) - 4] = 0;
                    strcat(temp_buffer, ".png");

                    if(file_exists(temp_buffer))
                    {
                        if(LoadTexturePNG(temp_buffer, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 120; FullScreen = 0;
                        }
                    }
                    else
                    {
                        temp_buffer[strlen(temp_buffer) - 4] = 0;
                        strcat(temp_buffer, ".jpg");

                        if(file_exists(temp_buffer))
                        {
                            if(LoadTextureJPG(temp_buffer, TEMP_PICT) == SUCCESS)
                            {
                                png_signal = 120; FullScreen = 0;
                            }
                        }
                    }
                }
            }
        }

        if(png_signal)
        {
            int h;

            if(Png_offset[TEMP_PICT])
            {
                tiny3d_SetTextureWrap(0, Png_offset[TEMP_PICT], Png_datas[TEMP_PICT].width,
                 Png_datas[TEMP_PICT].height, Png_datas[TEMP_PICT].wpitch,
                 TINY3D_TEX_FORMAT_A8R8G8B8,  TEXTWRAP_CLAMP, TEXTWRAP_CLAMP,1);

                if (FullScreen == 1)
                {
                    if (Png_datas[TEMP_PICT].width>=Png_datas[TEMP_PICT].height)
                    {
                        h = Png_datas[TEMP_PICT].height > 480 ? 480 : Png_datas[TEMP_PICT].height;
                        img_width = h * Png_datas[TEMP_PICT].width / Png_datas[TEMP_PICT].height * 512/480;
                    }
                    else
                    {
                        img_width = Png_datas[TEMP_PICT].width > 848 ? 848 : Png_datas[TEMP_PICT].width;
                        h = img_width * Png_datas[TEMP_PICT].height / Png_datas[TEMP_PICT].width  * 512/480;
                    }

                    DrawBox((Video_Resolution.width-img_width) / 2, (Video_Resolution.height - h) / 2, 0, img_width, h, 0xffffff40);
                    DrawTextBox((848-img_width) / 2, (480 - h) / 2, 0, img_width, h, WHITE);

                }
                else
                {
                    img_width = (use_split && is_vsplit) ? 300 : 160;
                    h = img_width * Png_datas[TEMP_PICT].height / Png_datas[TEMP_PICT].width  * 512/480;
                    if ((img_width == 160) && (h < 160))
                    {
                        img_width = 300;
                        h = img_width * Png_datas[TEMP_PICT].height / Png_datas[TEMP_PICT].width  * 512/480;
                    }

                    DrawBox((!fm_pane || !use_split) ? 848 - img_width : 0, use_split ? 512 - h - 32 :
                            (fm_pane ? 256 - h : 512 - h), 0, img_width, h, 0xffffff40);

                    DrawTextBox((!fm_pane || !use_split) ? 848 - img_width : 0, use_split ? 512 - h - 32 :
                                (fm_pane ? 256 - h : 512 - h), 0, img_width, h, WHITE);
                }
            }

            png_signal--;
            if(png_signal <= 0) FullScreen = 0;
        }

        // end auto PNG


        // popup menu

        if(set_menu2)
        {
            int py = 0;
            int max_menu2 = 8; bool is_dir=false;
            if((!fm_pane && (path1[1] == 0)) || (fm_pane && (path2[1] == 0))) max_menu2 = 6;
            else if(!fm_pane &&
                    (strcmp(path1, "/dev_hdd0/game") == SUCCESS ||
                     strstr(path1, "/GAME") != NULL ||
                     strcmp(entries1[sel1].d_name, "game") == SUCCESS ||
                     strcmp(entries1[sel1].d_name, "GAMES") == SUCCESS ||
                     strcmp(entries1[sel1].d_name, "GAMEZ") == SUCCESS ||
                     (strstr(path1, "/PS3ISO") != NULL &&
                     (!strcmpext(entries1[sel1].d_name, ".iso") || !strcmpext(entries1[sel1].d_name, ".iso.0")))
                   )) max_menu2 = 9;
            else if(fm_pane &&
                    (strcmp(path2, "/dev_hdd0/game") == SUCCESS ||
                     strstr(path2, "/GAME") != NULL ||
                     strcmp(entries2[sel2].d_name, "game") == SUCCESS ||
                     strcmp(entries2[sel2].d_name, "GAMES") == SUCCESS ||
                     strcmp(entries2[sel2].d_name, "GAMEZ") == SUCCESS ||
                     (strstr(path2, "/PS3ISO")  != NULL &&
                     (!strcmpext(entries2[sel2].d_name, ".iso") || !strcmpext(entries2[sel2].d_name, ".iso.0")))
                   )) max_menu2 = 9;
            else if( (!fm_pane && use_cobra && (entries1[sel1].d_type & IS_DIRECTORY) && strstr(path1, "/dev_bdvd")==NULL && !is_ntfs_path(path1))   ||
                     ( fm_pane && use_cobra && (entries2[sel2].d_type & IS_DIRECTORY) && strstr(path2, "/dev_bdvd")==NULL && !is_ntfs_path(path2)) ) {max_menu2 = 9; is_dir=true;}
            else if( (!fm_pane && use_cobra && is_ntfs_path(path1) && !(entries1[sel1].d_type & IS_DIRECTORY)) || ( fm_pane && use_cobra && is_ntfs_path(path2) && !(entries2[sel2].d_type & IS_DIRECTORY) ) ) {max_menu2 = 9;}

            //else if(!(!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY)) || !(fm_pane && (entries2[sel2].d_type & IS_DIRECTORY))) {max_menu2 = 9;}


            DrawBox((848 - 224)/2, (512 - (24 * max_menu2 + 1))/2 - 20 - 20, 0, 224, (24 * max_menu2 + 1) + 40, GRAY);
            DrawBox((848 - 216)/2, (512 - (24 * (max_menu2 + 1)))/2 - 20, 0, 216, (24 * (max_menu2 + 1)), POPUPMENUCOLOR);
            set_ttf_window((848 - 200)/2, (512 - (24 * (max_menu2 + 1)) - 20)/2, 200, (24 * (max_menu2 + 1)), 0);

            if(new_pad & BUTTON_CROSS_) frame = 300;

            if(max_menu2 == 6)
            {
                if(use_cobra == false || bAllowNetGames == false) mount_option = 0;

                bool blink = (set_menu2 == 1  && (frame & BLINK));

                display_ttf_string(0, py, (mount_option == 1) ? "Mount /net_host0" :
                                          (mount_option == 2) ? "Mount /net_host0/PKG" :
                                          (mount_option == 3) ? "Mount /net_host0/VIDEO" :
                                          (mount_option == 4) ? "Mount /net_host1" :
                                          (mount_option == 5) ? "Mount /net_host1/PKG" :
                                          (mount_option == 6) ? "Mount /net_host1/VIDEO" :
                                          (mount_option == 7) ? "Unmount /dev_bdvd" :
                                          !dev_blind ? "Mount /dev_blind" : "Unmount /dev_blind", blink ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, "LV2 Dump",          (set_menu2 == 2  && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, "LV1 Dump",          (set_menu2 == 3  && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, "RAM Editor",        (set_menu2 == 4  && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, "LV2 Editor",        (set_menu2 == 5  && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, (exit_option == 1) ? "Exit to XMB" : (exit_option == 2) ? "Restart the PS3" : "Exit File Manager",
                                                               (set_menu2 == 6  && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;
            }
            else
            {
                display_ttf_string(0, py, "New Folder",        (set_menu2 == 1 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, "Rename",            (set_menu2 == 2 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                if(allow_shadow_copy && !strncmp(path1, "/dev_hdd0", 9) && !strncmp(path1, path2, 9))
                {
                    display_ttf_string(0, py, "Shadow Copy",   (set_menu2 == 3 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;
                }
                else
                {
                    allow_shadow_copy = false;
                    display_ttf_string(0, py, "Copy",          (set_menu2 == 3  && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;
                }

                display_ttf_string(0, py, "Move",              (set_menu2 == 4 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, "Delete",            (set_menu2 == 5 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, "Paste to New File", (set_menu2 == 6 && (frame & BLINK)) ? INVISIBLE : copy_len ? WHITE : GRAY, 0, 16, 24); py += 24;

                display_ttf_string(0, py, ((!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY)) || ( fm_pane && (entries2[sel2].d_type & IS_DIRECTORY))) ?
                                          "Build ISO from Folder" : "Build ISO from File",
                                                               (set_menu2 == 7 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                display_ttf_string(0, py, ((!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY)) || ( fm_pane && (entries2[sel2].d_type & IS_DIRECTORY))) ?
                                          "Get Folder Info" : "Get File Info",
                                                               (set_menu2 == 8 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;

                if(is_dir)
                    {display_ttf_string(0, py, (mnt_mode == 1) ? "Mount + Exit to XMB" : (mnt_mode == 2) ? "Fix Permissions" : "Mount Folder",
                                                               (set_menu2 == 9 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;}
                else if(max_menu2 >= 9)
                {
                    //if(mnt_mode > 1) mnt_mode = 0;

                    if( (!fm_pane && (!strcmpext(entries1[sel1].d_name, ".iso") || !strcmpext(entries1[sel1].d_name, ".iso.0"))) ||
                        ( fm_pane && (!strcmpext(entries2[sel2].d_name, ".iso") || !strcmpext(entries2[sel2].d_name, ".iso.0"))) )
                        {display_ttf_string(0, py, "Fix Game", (set_menu2 == 9 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;}
                    else if((!fm_pane && use_cobra && is_ntfs_path(path1)) || ( fm_pane && use_cobra && is_ntfs_path(path2)))
                        {display_ttf_string(0, py, (mnt_mode == 1) ? "Mount + Exit to XMB" : (mnt_mode == 2) ? "Make Fake ISO" : "Mount as /dev_bdvd",
                                                               (set_menu2 == 9 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;}

                    //else if(!(!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY)) || !(fm_pane && (entries2[sel2].d_type & IS_DIRECTORY)))
                    //    {display_ttf_string(0, py, (mnt_mode == 1) ? "Mount + Exit to XMB" : (mnt_mode == 2) ? "Make Fake ISO" : "Mount as /dev_bdvd",
                    //                                           (set_menu2 == 9 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;}

                    else
                        {display_ttf_string(0, py, "Fix Game", (set_menu2 == 9 && (frame & BLINK)) ? INVISIBLE : WHITE, 0, 16, 24); py += 24;}
                }
            }
        }
        else
            allow_shadow_copy = true;


        // help

        if(help)
        {
            DrawBox((848 - 624)/2, (512 - 424)/2, 0, 624, 424, GRAY);
            DrawBox((848 - 616)/2, (512 - 416)/2, 0, 616, 416, POPUPMENUCOLOR);
            set_ttf_window((848 - 600)/2, (512 - 416)/2, 600, 416, WIN_AUTO_LF);

            if(set_menu2)
                display_ttf_string(0, 0, help2, WHITE, 0, 16, 24);
            else
                display_ttf_string(0, 0, help1, WHITE, 0, 16, 24);
        }

        if(!(old_pad & BUTTON_SELECT) && (new_pad & BUTTON_START)) help ^= 1;

        if((new_pad & BUTTON_CIRCLE_) && help) {help ^= 1; new_pad ^= BUTTON_CIRCLE_;}

        if(help) continue;


        // return to game list / xmb

        if (old_pad & BUTTON_SELECT)
        {
            if(new_pad & BUTTON_START) break;
            else if(new_pad & BUTTON_CIRCLE_)
            {
                if(DrawDialogYesNo("Exit to XMB?") == YES) {fun_exit(); SaveGameList(); exit(0);}
                new_pad = 0;
            }
        }

        if((new_pad & BUTTON_TRIANGLE) && (old_pad & BUTTON_SELECT)) set_menu2 = 0;

        else if((new_pad & BUTTON_TRIANGLE) || (new_pad & BUTTON_CIRCLE_))
        {
            if(FullScreen == 1) {png_signal = 120; FullScreen = 0; continue;}
            if(!fm_pane && nentries1) set_menu2 = !set_menu2;
            if(fm_pane && nentries2) set_menu2 = !set_menu2;
        }

        //if((new_pad & (BUTTON_TRIANGLE)) && set_menu2) {set_menu2 = 0; new_pad ^= BUTTON_TRIANGLE;}
        //if((new_pad & (BUTTON_CIRCLE_)) && set_menu2) {set_menu2 = 0; new_pad ^= BUTTON_CIRCLE_;}


        // execute popup-menu option

        if(set_menu2)
        {
            int max_menu2 = 8; bool is_dir=false;
            if((!fm_pane && (path1[1] == 0)) || (fm_pane && (path2[1] == 0))) max_menu2 = 6;
            else if(!fm_pane &&
                    (strcmp(path1, "/dev_hdd0/game") == SUCCESS ||
                     strstr(path1, "/GAME") != NULL ||
                     strcmp(entries1[sel1].d_name, "game") == SUCCESS ||
                     strcmp(entries1[sel1].d_name, "GAMES") == SUCCESS ||
                     strcmp(entries1[sel1].d_name, "GAMEZ") == SUCCESS ||
                     (strstr(path1, "/PS3ISO") != NULL &&
                     (!strcmpext(entries1[sel1].d_name, ".iso") || !strcmpext(entries1[sel1].d_name, ".iso.0")))
                   )) max_menu2 = 9;
            else if(fm_pane &&
                    (strcmp(path2, "/dev_hdd0/game") == SUCCESS ||
                     strstr(path2, "/GAME") != NULL ||
                     strcmp(entries2[sel2].d_name, "game") == SUCCESS ||
                     strcmp(entries2[sel2].d_name, "GAMES") == SUCCESS ||
                     strcmp(entries2[sel2].d_name, "GAMEZ") == SUCCESS ||
                     (strstr(path2, "/PS3ISO")  != NULL &&
                     (!strcmpext(entries2[sel2].d_name, ".iso") || !strcmpext(entries2[sel2].d_name, ".iso.0")))
                   )) max_menu2 = 9;
            else if( (!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY) && strstr(path1, "/dev_bdvd")==NULL && !is_ntfs_path(path1))   ||
                     ( fm_pane && (entries2[sel2].d_type & IS_DIRECTORY) && strstr(path2, "/dev_bdvd")==NULL && !is_ntfs_path(path2)) ) {max_menu2 = 9; is_dir=true;}
            else if( (!fm_pane && use_cobra && is_ntfs_path(path1) && !(entries1[sel1].d_type & IS_DIRECTORY)) || ( fm_pane && use_cobra && is_ntfs_path(path2) && !(entries2[sel2].d_type & IS_DIRECTORY) ) ) {max_menu2 = 9;}

            //else if(!(!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY)) || !(fm_pane && (entries2[sel2].d_type & IS_DIRECTORY))) {max_menu2 = 9;}

            if(new_pad & BUTTON_UP)
                ROT_DEC(set_menu2, 1, max_menu2)
            else if(new_pad & BUTTON_DOWN)
                ROT_INC(set_menu2, max_menu2, 1)
            else if((set_menu2 == 1) && (max_menu2 == 6))
            {
                if(new_pad & BUTTON_LEFT)
                    ROT_DEC(mount_option, 0, 7)
                else if(new_pad & BUTTON_RIGHT)
                    ROT_INC(mount_option, 7, 0)
                else if(new_pad & BUTTON_SELECT)
                    mount_option = 0;
            }
            else if((set_menu2 == 6) && (max_menu2 == 6))
            {
                if(new_pad & BUTTON_LEFT)
                    ROT_DEC(exit_option, 0, 2)
                else if(new_pad & BUTTON_RIGHT)
                    ROT_INC(exit_option, 2, 0)
                else if(new_pad & BUTTON_SELECT)
                    exit_option = 0;
            }
            else if(set_menu2 == 9)
            {
                if(new_pad & BUTTON_LEFT)
                    ROT_DEC(mnt_mode, 0, 2)
                else if(new_pad & BUTTON_RIGHT)
                    ROT_INC(mnt_mode, 2, 0)
                else if(new_pad & BUTTON_SELECT)
                    mnt_mode = 0;
            }
            else
            if((set_menu2 == 3) && (max_menu2 != 6) && ((new_pad & BUTTON_LEFT) || (new_pad & BUTTON_RIGHT) || (new_pad & BUTTON_SELECT)))
            {
                allow_shadow_copy = !allow_shadow_copy;
            }

         if(new_pad & BUTTON_CROSS_)
         {
            char buffer1[256];
            frame = 300; //force immediate refresh

            if(options_locked)
            {
                if(set_menu2 != 7)
                {
                    DrawDialogOKTimer("Locked by Parental Control", 2000.0f);
                    set_menu2 = 666; // for skip
                }
            }

            if(max_menu2 == 6)
            {
                if(set_menu2 == 1)
                {
                    if(mount_option)
                    {
                        if(bAllowNetGames && get_net_status() == SUCCESS)
                        {
                            if(mount_option == 1)
                            {
                                download_file("http://localhost/mount_ps3/net0/.", NULL, 0, NULL);
                                DrawDialogTimer("Mounted /net_host0 as local /dev_bdvd", 2000.0f);
                            }
                            else if(mount_option == 2)
                            {
                                download_file("http://localhost/mount_ps3/net0/PKG", NULL, 0, NULL);
                                DrawDialogTimer("Mounted /net_host0/PKG as local /dev_bdvd", 2000.0f);
                            }
                            else if(mount_option == 3)
                            {
                                download_file("http://localhost/mount_ps3/net0/VIDEO", NULL, 0, NULL);
                                DrawDialogTimer("Mounted /net_host0/VIDEO as local /dev_bdvd", 2000.0f);
                            }
                            else if(mount_option == 4)
                            {
                                download_file("http://localhost/mount_ps3/net1/.", NULL, 0, NULL);
                                DrawDialogTimer("Mounted /net_host1 as local /dev_bdvd", 2000.0f);
                            }
                            else if(mount_option == 5)
                            {
                                download_file("http://localhost/mount_ps3/net1/PKG", NULL, 0, NULL);
                                DrawDialogTimer("Mounted /net_host1/PKG as local /dev_bdvd", 2000.0f);
                            }
                            else if(mount_option == 6)
                            {
                                download_file("http://localhost/mount_ps3/net1/VIDEO", NULL, 0, NULL);
                                DrawDialogTimer("Mounted /net_host1/VIDEO as local /dev_bdvd", 2000.0f);
                            }
                            else if(mount_option == 7)
                            {
                                download_file("http://localhost/mount.ps3/unmount", NULL, 0, NULL);
                                DrawDialogTimer("Unmounted /dev_bdvd", 2000.0f);

                                if(!strncmp(path1, "/dev_bdvd", 9)) {path1[1] = 0; nentries1 = 0;}
                                if(!strncmp(path2, "/dev_bdvd", 9)) {path2[1] = 0; nentries2 = 0;}
                            }

                            if(mount_option != 7 && file_exists("/dev_bdvd"))
                            {
                                if(!fm_pane)
                                {
                                    sprintf(path1, "/dev_bdvd");
                                    nentries1 = 0;
                                }
                                else
                                {
                                    sprintf(path2, "/dev_bdvd");
                                    nentries2 = 0;
                                }
                            }
                        }
                    }
                    else
                    {
                        // mount/umount /dev_blind
                        if(dev_blind)
                        {
                            sys_fs_umount("/dev_blind");
                            sys_fs_umount("/dev_habib");
                            sys_fs_umount("/dev_rebug");
                            sys_fs_umount("/dev_rewrite");

                            dev_blind = false;

                            // return to root
                            if(!strncmp(path1, "/dev_blind", 10) ||
                               !strncmp(path1, "/dev_habib", 10) ||
                               !strncmp(path1, "/dev_rebug", 10) ||
                               !strncmp(path1, "/dev_rewrite", 12)) path1[1] = 0;

                            if(!strncmp(path2, "/dev_blind", 10) ||
                               !strncmp(path2, "/dev_habib", 10) ||
                               !strncmp(path2, "/dev_rebug", 10) ||
                               !strncmp(path2, "/dev_rewrite", 12)) path2[1] = 0;
                        }
                        else
                            dev_blind = (sys_fs_mount("CELL_FS_IOS:BUILTIN_FLSH1", "CELL_FS_FAT", "/dev_blind", 0) == SUCCESS);
                    }

                    nentries1 = pos1 = sel1 = 0;
                    nentries2 = pos2 = sel2 = 0;

                } // mount/umount /dev_blind
                else if(set_menu2 == 2 || set_menu2 == 3)
                {   // lv2 / lv1 dump
                    sprintf(temp_buffer, "/%s", !fm_pane ? entries1[sel1].d_name : entries2[sel2].d_name);

                    if(strncmp(temp_buffer, "/dev_flash", 10) == SUCCESS || strstr("/host_root|/app_home|/dev_bdvd|/dev_blind|/dev_habib|/dev_rewrite|/dev_rebug|/dev_ps2disc", temp_buffer) != NULL)
                        strcpy(temp_buffer, "/dev_hdd0");

                    int flen = strlen(temp_buffer);

                    int ret = level_dump(temp_buffer, 0x800400ULL, (set_menu2 == 3) ? 1 : 2);

                    if(ret < 0)
                    {
                        sprintf(MEM_MESSAGE, "Error in %s dump: 0x%08x\n\n%s", (set_menu2 == 3) ? "LV1" : "LV2", ret, getlv2error(ret));
                        DrawDialogOK(MEM_MESSAGE);
                    }
                    else
                    if(!fm_pane)
                    {
                        update_device_sizes |= 1;
                        nentries1 = pos1 = sel1 = 0;
                        strncpy(path1, temp_buffer, flen);
                    }
                    else
                    {
                        update_device_sizes |= 2;
                        nentries2 = pos2 = sel2 = 0;
                        strncpy(path2, temp_buffer, flen);
                    }

                }   // lv2 / lv1 dump
                else if(set_menu2 == 4)
                {   // RAM area editor
                    hex_editor(HEX_EDIT_RAM, "RAM Area Editor", 0x10000000ULL);
                    frame = set_menu2 = 0;
                    continue;

                }   // RAM area editor
                else if(set_menu2 == 5)
                {   // LV2 editor
                    hex_editor(HEX_EDIT_LV2, "LV2 Editor", 0x800000ULL);
                    frame = set_menu2 = 0;
                    continue;

                }   // LV2 Editor
                else if(set_menu2 == 6)
                {
                    if(exit_option == 1)
                    {
                        if(DrawDialogYesNo("Exit to XMB?") == YES) {unlink_secure("/dev_hdd0/tmp/wm_request"); fun_exit(); SaveGameList(); exit(0);}
                    }
                    else
                    if(exit_option == 2)
                    {
                        if(DrawDialogYesNo("Restart the PS3?") == YES) {unlink_secure("/dev_hdd0/tmp/wm_request"); fun_exit(); set_install_pkg = true; SaveGameList(); sys_reboot();}
                    }
                    else
                    {
                        // Return to Game List
                        set_menu2 = 0;
                        break;
                    }
                    continue;
                }   // Exit File Manager
            }
            else if(set_menu2 == 1)
            {
                // new folder
                sprintf(buffer1, "%s", "New");

                if(Get_OSK_String("New Folder", buffer1, 256) == SUCCESS)
                {
                     if(buffer1[0] == 0) {set_menu2 = 0; continue;}

                     sprintf(MEM_MESSAGE, "Do you want to create the new folder %s\non %s ?", buffer1, !fm_pane ? path1 : path2);

                     ps3pad_read();

                     if((old_pad | BUTTON_L2) || DrawDialogYesNo(MEM_MESSAGE) == YES)
                     {
                         exitcode = REFRESH_GAME_LIST;

                         if(!fm_pane)
                            sprintf(TEMP_PATH, "%s/%s", path1, buffer1);
                         else
                            sprintf(TEMP_PATH, "%s/%s", path2, buffer1);

                         int ret;

                         ret = mkdir_secure(TEMP_PATH);

                         if(ret < 0)
                         {
                            sprintf(MEM_MESSAGE, "New folder error: 0x%08x\n\n%s", ret, getlv2error(ret));
                            DrawDialogOK(MEM_MESSAGE);
                         }

                         if(strcmp(path1, path2) == SUCCESS)
                            {update_device_sizes |= 1|2; pos1 = sel1 = nentries1 = pos2 = sel2 = nentries2 = 0;}
                         else if(fm_pane)
                            {update_device_sizes |= 2; pos2 = sel2 = nentries2 = 0;}
                         else
                            {update_device_sizes |= 1; pos1 = sel1 = nentries1 = 0;}

                         frame = 300; //force immediate refresh
                     }
                }

            } // new folder
            else if(set_menu2 == 2)
            {
                if(!fm_pane)
                   strcpy(buffer1, entries1[sel1].d_name);
                else
                   strcpy(buffer1, entries2[sel2].d_name);

                if(Get_OSK_String("Rename", buffer1, 256) == SUCCESS)
                {
                     if(buffer1[0] == 0 || (!fm_pane && !strcmp(buffer1, entries1[sel1].d_name))
                                        || ( fm_pane && !strcmp(buffer1, entries2[sel2].d_name))) {set_menu2 = 0; continue;}

                     sprintf(MEM_MESSAGE, "Do you want to rename %s\nto %s ?",
                                          !fm_pane ? entries1[sel1].d_name : entries2[sel2].d_name, buffer1);

                     ps3pad_read();

                     if((old_pad | BUTTON_L2) || DrawDialogYesNo(MEM_MESSAGE) == YES)
                     {
                         exitcode = REFRESH_GAME_LIST;

                         if(!fm_pane)
                         {
                            sprintf(TEMP_PATH1, "%s/%s", path1, entries1[sel1].d_name);
                            sprintf(TEMP_PATH2, "%s/%s", path1, buffer1);
                         }
                         else
                         {
                            sprintf(TEMP_PATH1, "%s/%s", path2, entries2[sel2].d_name);
                            sprintf(TEMP_PATH2, "%s/%s", path2, buffer1);
                         }

                         int ret = rename_secure(TEMP_PATH1, TEMP_PATH2);

                         if(ret < 0)
                         {
                            sprintf(MEM_MESSAGE, "Rename error: 0x%08x\n\n%s", ret, getlv2error(ret));
                            DrawDialogOK(MEM_MESSAGE);
                         }

                         if(strcmp(path1, path2) == SUCCESS)
                            {update_device_sizes |= 1|2; pos1 = sel1 = nentries1 = pos2 = sel2 = nentries2 = 0;}
                         else if(fm_pane)
                            {update_device_sizes |= 2; pos2 = sel2 = nentries2 = 0;}
                         else
                            {update_device_sizes |= 1; pos1 = sel1 = nentries1 = 0;}

                         frame = 300; //force immediate refresh
                     }
                }

            } // rename
            else if(set_menu2 == 3)
            {
                // copy
                int files;
                int ret = 0;

                if(!fm_pane)
                {
                    if(test_mark_flags(entries1, nentries1, &files))
                    {
                        // multiple
                        if((path2[1] == 0) || !strcmp(path1, path2)) {set_menu2 = 0; continue;}

                        ret = copy_file_manager(path1, path2, entries1, nentries1, -1, free_device2);
                        exitcode = REFRESH_GAME_LIST;
                    }
                    else
                    {
                        if(!strcmp(entries1[sel1].d_name, "..") || (path2[1] == 0) || !strcmp(path1, path2)) {set_menu2 = 0; continue;}

                        ret = copy_file_manager(path1, path2, entries1, nentries1, sel1, free_device2);
                        exitcode = REFRESH_GAME_LIST;
                    }
                }
                else
                {
                    if(test_mark_flags(entries2, nentries2, &files))
                    {
                        // multiple
                        if((path1[1] == 0) || !strcmp(path1, path2)) {set_menu2 = 0; continue;}

                        ret = copy_file_manager(path2, path1, entries2, nentries2, -1, free_device1);
                        exitcode = REFRESH_GAME_LIST;
                    }
                    else
                    {
                        if(!strcmp(entries2[sel2].d_name, "..") || (path1[1] == 0) || !strcmp(path1, path2)) {set_menu2 = 0; continue;}

                        ret = copy_file_manager(path2, path1, entries2, nentries2, sel2, free_device1);
                        exitcode = REFRESH_GAME_LIST;
                    }
                }

                if(ret < 0)
                {
                    sprintf(MEM_MESSAGE, "Copy error: 0x%08x\n\n%s", ret, getlv2error(ret));
                    DrawDialogOK(MEM_MESSAGE);
                }

                if(strcmp(path1, path2) == SUCCESS)
                    {update_device_sizes |= 1|2; pos1 = sel1 = nentries1 = pos2 = sel2 = nentries2 = 0;}
                else if(!fm_pane)
                    {update_device_sizes |= 2; pos2 = sel2 = nentries2 = 0;}
                else
                    {update_device_sizes |= 1; pos1 = sel1 = nentries1 = 0;}

                frame = 300; //force immediate refresh

            } // copy
            else if(set_menu2 == 4)
            {
                // move
                int files;
                int ret = 0;

                if(!fm_pane)
                {
                    if(test_mark_flags(entries1, nentries1, &files))
                    {
                        // multiple
                        if((path2[1] == 0) || !strcmp(path1, path2))  {set_menu2 = 0; continue;}

                        ret = move_file_manager(path1, path2, entries1, nentries1, -1, free_device2);
                        exitcode = REFRESH_GAME_LIST;
                    }
                    else
                    {
                        if(!strcmp(entries1[sel1].d_name, "..") || (path2[1] == 0)  || !strcmp(path1, path2)) {set_menu2 = 0; continue;}

                        ret = move_file_manager(path1, path2, entries1, nentries1, sel1, free_device2);
                        exitcode = REFRESH_GAME_LIST;
                    }
                }
                else
                {
                    if(test_mark_flags(entries2, nentries2, &files))
                    {
                        // multiple
                        if((path1[1] == 0) || !strcmp(path1, path2)) {set_menu2 = 0; continue;}

                        ret = move_file_manager(path2, path1, entries2, nentries2, -1, free_device1);
                        exitcode = REFRESH_GAME_LIST;
                    }
                    else
                    {
                        if(!strcmp(entries2[sel2].d_name, "..") || (path1[1] == 0)  || !strcmp(path1, path2)) {set_menu2 = 0; continue;}

                        ret = move_file_manager(path2, path1, entries2, nentries2, sel2, free_device1);
                        exitcode = REFRESH_GAME_LIST;
                    }
                }

                 if(ret < 0)
                 {
                    sprintf(MEM_MESSAGE, "Move error: 0x%08x\n\n%s", ret, getlv2error(ret));
                    DrawDialogOK(MEM_MESSAGE);
                 }

                 update_device_sizes |= 1|2;
                 nentries1 = pos1 = sel1 = 0;
                 nentries2 = pos2 = sel2 = 0;
                 frame = 300; //force immediate refresh

            } // move
            else if(set_menu2 == 5)
            {
                // delete
                sysFSDirent *entries;
                int nentries, sel;
                char *path;

                int files;
                int ret = 0;
                int cfiles = 0;

                if(!fm_pane)
                {
                    entries = entries1;
                    nentries = nentries1;
                    sel = sel1;
                    path = path1;
                    update_device_sizes |= 1;
                }
                else
                {
                    entries = entries2;
                    nentries = nentries2;
                    sel = sel2;
                    path = path2;
                    update_device_sizes |= 2;
                }

                if(test_mark_flags(entries, nentries, &files))
                {
                    // multiple
                    sprintf(MEM_MESSAGE, "Do you want to delete the selected Files and Folders?\n\n(%i) Items", files);

                    if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                    {
                        exitcode = REFRESH_GAME_LIST;

                        single_bar("Deleting...");

                        float parts = 100.0f / (float) files;
                        float cpart = 0;

                        for(n = 0; n < nentries; n++)
                        {
                            if(!(entries[n].d_type & IS_MARKED)) continue; // skip no marked
                            if(progress_action == 2) break;

                            cpart += parts;
                            if(cpart >= 1.0f)
                            {
                                update_bar((u32) cpart);
                                cpart-= (float) ((u32) cpart);
                            }
                            cfiles++;

                            sprintf(temp_buffer, "%s/%s", path, entries[n].d_name);

                            if(entries[n].d_type & IS_DIRECTORY)
                            {
                                DeleteDirectory(temp_buffer);
                                if(is_ntfs_path(temp_buffer))
                                    ret = ps3ntfs_unlink(temp_buffer);
                                else
                                    ret = rmdir_secure(temp_buffer);

                            }
                            else
                            {
                                if(is_ntfs_path(temp_buffer))
                                    ret = ps3ntfs_unlink(temp_buffer);
                                else
                                    ret = unlink_secure(temp_buffer);
                            }

                            if(ret < 0) break;
                        }
                        sysUtilCheckCallback(); tiny3d_Flip();
                        msgDialogAbort();
                        usleep(250000);

                        if(ret < 0)
                        {
                            sprintf(MEM_MESSAGE, "Delete error: 0x%08x\n\n%s", ret, getlv2error(ret));
                            DrawDialogOK(MEM_MESSAGE);
                        }

                        if(strcmp(path1, path2) == SUCCESS)
                           {update_device_sizes |= 1|2; pos1 = sel1 = nentries1 = pos2 = sel2 = nentries2 = 0;}
                        else if(fm_pane)
                           {update_device_sizes |= 2; pos2 = sel2 = nentries2 = 0;}
                        else
                           {update_device_sizes |= 1; pos1 = sel1 = nentries1 = 0;}

                        frame = 300; //force immediate refresh
                    }
                }
                else
                {
                    if(!strcmp(entries[sel].d_name, "..")) {set_menu2 = 0; continue;}

                    sprintf(MEM_MESSAGE, "Do you want to delete %s?", entries[sel].d_name);

                    if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                    {
                        sprintf(temp_buffer, "%s/%s", path, entries[sel].d_name);

                        if(entries[sel].d_type & IS_DIRECTORY)
                        {
                            DeleteDirectory(temp_buffer);
                            if(is_ntfs_path(temp_buffer))
                                ret = ps3ntfs_unlink(temp_buffer);
                            else
                                ret = rmdir_secure(temp_buffer);
                        }
                        else
                        {
                            if(is_ntfs_path(temp_buffer))
                                ret = ps3ntfs_unlink(temp_buffer);
                            else
                                ret = unlink_secure(temp_buffer);
                        }

                        if(ret < 0)
                        {
                            sprintf(MEM_MESSAGE, "Delete error: 0x%08x\n\n%s", ret, getlv2error(ret));
                            DrawDialogOK(MEM_MESSAGE);
                        }

                        if(strcmp(path1, path2) == SUCCESS)
                           {update_device_sizes |= 1|2; pos1 = sel1 = nentries1 = pos2 = sel2 = nentries2 = 0;}
                        else if(fm_pane)
                           {update_device_sizes |= 2; pos2 = sel2 = nentries2 = 0;}
                        else
                           {update_device_sizes |= 1; pos1 = sel1 = nentries1 = 0;}

                        frame = 300; //force immediate refresh
                    }
                }

            } // delete
            else if(set_menu2 == 6)
            {
                // Paste to New File
                if(copy_len == 0 || !copy_mem) {DrawDialogOKTimer("Paste buffer is empty", 2000.0f); set_menu2 = 0; continue;}

                sprintf(buffer1, "%s", "Newfile");

                if(Get_OSK_String("Paste to New File", buffer1, 256) == SUCCESS)
                {
                     if(buffer1[0] == 0) {DrawDialogOKTimer("Invalid filename", 2000.0f); set_menu2 = 0; continue;}

                     ps3pad_read();

                     sprintf(MEM_MESSAGE, "Do you want to create the new file %s.bin\non %s ?", buffer1, !fm_pane ? path1 : path2);

                     if((old_pad | BUTTON_L2) || DrawDialogYesNo(MEM_MESSAGE) == YES)
                     {
                         exitcode = REFRESH_GAME_LIST;

                         if(!fm_pane)
                         {
                            update_device_sizes |= 1;
                            sprintf(temp_buffer, "%s/%s.bin", path1, buffer1);
                         }
                         else
                         {
                            update_device_sizes |= 2;
                            sprintf(temp_buffer, "%s/%s.bin", path2, buffer1);
                         }

                         s32 fd = FAILED;

                         int ret;

                         is_ntfs = is_ntfs_path(temp_buffer);

                         if(is_ntfs) {fd = ps3ntfs_open(temp_buffer, O_WRONLY | O_CREAT | O_TRUNC, 0);if(fd < 0) ret = FAILED; else ret = SUCCESS;}
                         else
                            ret = sysLv2FsOpen(temp_buffer, SYS_O_WRONLY | SYS_O_CREAT | SYS_O_TRUNC, &fd, 0777, NULL, 0);

                         if(ret == SUCCESS && fd >= SUCCESS)
                         {
                            if(!is_ntfs) sysLv2FsChmod(temp_buffer, FS_S_IFMT | 0777);
                            ret = save_hex(is_ntfs, fd, 0LL, copy_mem, copy_len);
                            if(fd >= SUCCESS) {if(is_ntfs) ps3ntfs_close(fd); else sysLv2FsClose(fd);}
                         }

                         if(ret != SUCCESS)
                         {
                            sprintf(MEM_MESSAGE, "New file error: 0x%08x\n\n%s", ret, getlv2error(ret));
                            DrawDialogOK(MEM_MESSAGE);
                         }
                         else
                         {
                            sprintf(temp_buffer, "%d Bytes written", copy_len);
                            DrawDialogOKTimer(temp_buffer, 2000.0f);
                         }

                         if(strcmp(path1, path2) == SUCCESS)
                            {update_device_sizes |= 1|2; pos1 = sel1 = nentries1 = pos2 = sel2 = nentries2 = 0;}
                         else if(fm_pane)
                            {update_device_sizes |= 2; pos2 = sel2 = nentries2 = 0;}
                         else
                            {update_device_sizes |= 1; pos1 = sel1 = nentries1 = 0;}

                         frame = 300; //force immediate refresh
                     }
                }

            } // Paste to New File
            else if(set_menu2 == 7)
            {
                // Build ISO from file
                if(( fm_pane == 0 && ((path1[1] == 0) || strcmp(entries1[sel1].d_name, "..") == SUCCESS)) ||
                    (fm_pane == 1 && ((path2[1] == 0) || strcmp(entries2[sel2].d_name, "..") == SUCCESS))) ;
                else if((fm_pane == 0 && (entries1[sel1].d_type & IS_DIRECTORY)) ||
                        (fm_pane == 1 && (entries2[sel2].d_type & IS_DIRECTORY)))
                {
                    if(!fm_pane)
                        sprintf(TEMP_PATH1, "%s/%s", path1, entries1[sel1].d_name);
                    else
                        sprintf(TEMP_PATH1, "%s/%s", path2, entries2[sel2].d_name);

                    menu_screen = SCR_TOOL_BUILD_ISO;
                    while(menu_screen != SCR_MENU_GAME_OPTIONS)
                    {
                        cls();
                        update_twat(false);
                        draw_device_mkiso(0, 0, -1, TEMP_PATH1);
                    }

                    menu_screen = SCR_MAIN_GAME_LIST;
                    exitcode = REFRESH_GAME_LIST;
                    frame = 0;
               }
               else
               {
                    sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/showtime.iso", self_path);

                    if(!fm_pane)
                        sprintf(TEMP_PATH2, "%s/%s", path1, entries1[sel1].d_name);
                    else
                        sprintf(TEMP_PATH2, "%s/%s", path2, entries2[sel2].d_name);

                    launch_iso_build(TEMP_PATH1, TEMP_PATH2, true);
               }
            } // Build ISO from file
            else if(set_menu2 == 8)
            {
                // Get file / folder info
                int nfiles = 0, nfolders = 0;
                u64 size = 0ULL;

                set_menu2 = 0;

                if((!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY) && strcmp(entries1[sel1].d_name, "..") != 0) ||
                   ( fm_pane && (entries2[sel2].d_type & IS_DIRECTORY) && strcmp(entries2[sel2].d_name, "..") != 0))
                    DrawDialogTimer("Scanning folder ...", 500.0f);

                if(!fm_pane)
                    sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                else
                    sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);

                if((!fm_pane && (path1[1] != 0) && strcmp(entries1[sel1].d_name, "..")) ||
                   ( fm_pane && (path2[1] != 0) && strcmp(entries2[sel2].d_name, ".."))
                  )
                {
                    CountFiles(TEMP_PATH, &nfiles, &nfolders, &size);

                    if(!((!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY)) || (fm_pane && (entries2[sel2].d_type & IS_DIRECTORY)))) nfiles = 1;

                    if(size == 1LL)
                        sprintf(MEM_MESSAGE, "%s\n\n%i Files, %i Folders\n\nTotal Size: 1 Byte", TEMP_PATH, nfiles, nfolders);
                    else if(size < 1024LL)
                        sprintf(MEM_MESSAGE, "%s\n\n%i Files, %i Folders\n\nTotal Size: %i Bytes", TEMP_PATH, nfiles, nfolders, (int) size);
                    else
                        if(size < 0x100000LL)
                            sprintf(MEM_MESSAGE, "%s\n\n%i Files, %i Folders\n\nTotal Size: %1.1f KB (%1.0f Bytes)", TEMP_PATH, nfiles, nfolders, (double) (size  / 1024LL), (double) size);
                        else if(size < 0x40000000LL)
                            sprintf(MEM_MESSAGE, "%s\n\n%i Files, %i Folders\n\nTotal Size: %1.1f MB (%1.0f Bytes)", TEMP_PATH, nfiles, nfolders, (double) (size / 0x100000LL), (double) size);
                        else
                            sprintf(MEM_MESSAGE, "%s\n\n%i Files, %i Folders\n\nTotal Size: %1.2f GB (%1.0f Bytes)", TEMP_PATH, nfiles, nfolders, ((double) size) / GIGABYTES, (double) size);

                    DrawDialogOK(MEM_MESSAGE);
                }
            } // Getfile / folder info
            else if(set_menu2 == 9 && max_menu2 >= 9)
            {
                 // Fix game / Mount folder
                 if(!fm_pane)
                     sprintf(temp_buffer, "%s/%s", path1, entries1[sel1].d_name);
                 else
                     sprintf(temp_buffer, "%s/%s", path2, entries2[sel2].d_name);

                 if(mnt_mode == 2)
                 {
                     if((fm_pane == 0 && (entries1[sel1].d_type & IS_DIRECTORY)) ||
                        (fm_pane == 1 && (entries2[sel2].d_type & IS_DIRECTORY)))
                     {
                        pause_music(1);

                        // sys8_perm_mode(1);
                        DCls();
                        FixDirectory(temp_buffer, 0);
                        DCls();
                        // sys8_perm_mode(0);

                        msgDialogAbort();
                        msgDialogClose(0);

                        pause_music(0);
                     }
                     else if(!fm_pane && use_cobra && is_ntfs_path(path1))
                     {
                         DrawDialogTimer("Creating fake ISO ...", 500.0f);

                         mkdir_secure("/dev_hdd0/tmp/wmtmp");

                         for(int s = 0; s < nentries1; s++)
                         {
                             if((entries1[s].d_type & IS_MARKED) || (selcount1==0 && s==sel1))
                             {
                                 int flen=strlen(entries1[s].d_name)-4;
                                 if((entries1[s].d_type & IS_DIRECTORY) || (flen>0 && strcasestr(".iso|.bin|.mdf|.img|so.0", entries1[s].d_name + flen)!=NULL)) ;
                                 else
                                 {
                                     sprintf(temp_buffer, "%s/%s", path1, entries1[s].d_name);
                                     sprintf(TEMP_PATH1, "/dev_hdd0/tmp/wmtmp/%s.iso", entries1[s].d_name);
                                     launch_iso_build(TEMP_PATH1, temp_buffer, false);
                                 }
                             }
                         }
                         strcpy(path1, "/dev_hdd0/tmp/wmtmp\0"); nentries1 = pos1 = sel1 = 0; update_device_sizes = 1|2;

                         if(get_net_status() != SUCCESS) continue;
                         download_file("http://localhost/refresh.ps3", NULL, 0, NULL);
                     }
                     else if(fm_pane && use_cobra && is_ntfs_path(path2))
                     {
                         DrawDialogTimer("Creating fake ISO ...", 500.0f);

                         mkdir_secure("/dev_hdd0/tmp/wmtmp");

                         for(int s = 0; s < nentries2; s++)
                         {
                             if((entries2[s].d_type & IS_MARKED) || (selcount2==0 && s==sel2))
                             {
                                 int flen=strlen(entries2[s].d_name)-4;
                                 if((entries2[s].d_type & IS_DIRECTORY) || (flen>0 && strcasestr(".iso|.bin|.mdf|.img|so.0", entries2[s].d_name + flen)!=NULL)) ;
                                 else
                                 {
                                     sprintf(temp_buffer, "%s/%s", path2, entries2[s].d_name);
                                     sprintf(TEMP_PATH2, "/dev_hdd0/tmp/wmtmp/%s.iso", entries2[s].d_name);
                                     launch_iso_build(TEMP_PATH2, temp_buffer, false);
                                 }
                             }
                         }
                         strcpy(path2, "/dev_hdd0/tmp/wmtmp\0"); nentries2 = pos2 = sel2 = 0; update_device_sizes = 1|2;

                         if(get_net_status() != SUCCESS) continue;
                         download_file("http://localhost/refresh.ps3", NULL, 0, NULL);
                     }
                     else
                         sysLv2FsChmod(temp_buffer, FS_S_IFMT | 0777);

                     mnt_mode  = 1;
                     set_menu2 = 0;
                     continue;
                 }

                 if( (!fm_pane && (!strcmpext(entries1[sel1].d_name, ".iso") || !strcmpext(entries1[sel1].d_name, ".iso.0"))) ||
                     ( fm_pane && (!strcmpext(entries2[sel2].d_name, ".iso") || !strcmpext(entries2[sel2].d_name, ".iso.0"))) )
                 {
                     if((!fm_pane && selcount1<2) || (fm_pane && selcount2<2))
                         patchps3iso(temp_buffer, 0);
                     else if(fm_pane == 0)
                     {
                         for(int s = 0; s < nentries1; s++)
                         {
                             if((entries1[s].d_type & IS_MARKED) &&
                                (!strcmpext(entries1[s].d_name, ".iso") || !strcmpext(entries1[s].d_name, ".iso.0")))
                             {
                                 sprintf(temp_buffer, "%s/%s", path1, entries1[s].d_name);
                                 patchps3iso(temp_buffer, 1);
                             }
                         }
                     }
                     else if(fm_pane == 1)
                     {
                         for(int s = 0; s < nentries2; s++)
                         {
                             if((entries2[s].d_type & IS_MARKED) &&
                                (!strcmpext(entries2[s].d_name, ".iso") || !strcmpext(entries2[s].d_name, ".iso.0")))
                             {
                                 sprintf(temp_buffer, "%s/%s", path2, entries2[s].d_name);
                                 patchps3iso(temp_buffer, 1);
                             }
                         }
                     }
                 }

                 //else if(use_cobra && !((!fm_pane && (entries1[sel1].d_type & IS_DIRECTORY)) || (fm_pane && (entries2[sel2].d_type & IS_DIRECTORY))))
                 else if(use_cobra && ( (!fm_pane && is_ntfs_path(path1)) || (fm_pane && is_ntfs_path(path2)) ))
                 {
                     sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/pkg.iso", self_path);

                     if(!fm_pane)
                         sprintf(TEMP_PATH2, "%s/%s", path1, entries1[sel1].d_name);
                     else
                         sprintf(TEMP_PATH2, "%s/%s", path2, entries2[sel2].d_name);

                     int flen = strlen(TEMP_PATH2) - 4;

                     cobra_send_fake_disc_eject_event();
                     usleep(4000);
                     cobra_umount_disc_image();

                     cobra_unset_psp_umd();
                     sys_map_path((char*)"/dev_bdvd", NULL);
                     sys_map_path((char*)"/app_home", NULL);

                     if(flen >= 0 && (strcasestr(".iso|.bin|.mdf|.img|so.0", TEMP_PATH2 + flen) != NULL))
                         launch_iso_game(TEMP_PATH2, DETECT_EMU_TYPE);
                     else
                     {
                         unlink_secure(TEMP_PATH1);
                         launch_iso_build(TEMP_PATH1, TEMP_PATH2, false);

                         if(!fm_pane)
                            {strcpy(path1, "/dev_bdvd\0"); nentries1 = pos1 = sel1 = 0;}
                         else
                            {strcpy(path2, "/dev_bdvd\0"); nentries2 = pos2 = sel2 = 0;}
                     }

                     if((mnt_mode == 1) || (old_pad & BUTTON_SELECT)) {fun_exit(); SaveGameList(); exit(0);}
                 }
                 else
                 if(is_dir)
                 {
                     cobra_send_fake_disc_eject_event();
                     usleep(4000);
                     cobra_umount_disc_image();

                     sys_map_path("/dev_bdvd", temp_buffer);
                     sys_map_path("/app_home", temp_buffer);

                     cobra_send_fake_disc_insert_event();

                     if(!fm_pane)
                        {strcpy(path1, "/dev_bdvd\0"); nentries1 = pos1 = sel1 = 0;}
                     else
                        {strcpy(path2, "/dev_bdvd\0"); nentries2 = pos2 = sel2 = 0;}

                     if(mnt_mode == 1 || (old_pad & BUTTON_SELECT)) {fun_exit(); SaveGameList(); exit(0);}
                 }
                 else
                 {
                    pause_music(1);
                    patch_error_09(temp_buffer, 0);

                    DCls();
                    FixDirectory(temp_buffer, 0);
                    DCls();

                    msgDialogAbort();
                    msgDialogClose(0);

                    pause_music(0);
                 }

            } // fix game

            set_menu2 = 0;
            continue;
         }

        }
        else
        {

        AUTO_BUTTON_REP2(auto_up, BUTTON_UP)
        AUTO_BUTTON_REP2(auto_down, BUTTON_DOWN)

        if(new_pad & BUTTON_L1)
        {
            if(FullScreen == 1) new_pad = BUTTON_UP;
            else if(!fm_pane)
            {
                auto_up = 1; if(sel1 > (is_vsplit ? 12 : 8)) {sel1 = sel1 - (is_vsplit ? 12 : 8);} else {sel1 = 0;}
                if(sel1 < pos1) {pos1 = pos1 - (is_vsplit ? 12 : 4);}
                if(pos1 < 0) {pos1 = 0;}

            }
            else
            {
                auto_up = 1; if(sel2 > (is_vsplit ? 12 : 8)) {sel2 = sel2 - (is_vsplit ? 12 : 8);} else {sel2 = 0;}
                if(sel2 < pos2) {pos2 = pos2 - (is_vsplit ? 12 : 4);}
                if(pos2 < 0) {pos2 = 0;}
            }
        }

        if(new_pad & BUTTON_R1)
        {
            if(FullScreen == 1) new_pad = BUTTON_DOWN;
            else if(!fm_pane)
            {
                auto_down = 1; if(sel1 < (nentries1-(is_vsplit ? 12 : 4))) {sel1 = sel1 + (is_vsplit ? 12 : 4);} else {sel1 = (nentries1 - 1);}
                if(sel1 > (pos1 + (is_vsplit ? 12 : 4))) {pos1 = pos1 + (is_vsplit ? 12 : 4);}
                if(pos1 > (nentries1 - 1)) {pos1 = sel1;}
            }
            else
            {
                auto_down = 1; if(sel2 < (nentries2-(is_vsplit ? 12 : 4))) {sel2 = sel2 + (is_vsplit ? 12 : 4);} else {sel2 = (nentries2 - 1);}
                if(sel2 > (pos2 + (is_vsplit ? 12 : 4))) {pos2 = pos2 + (is_vsplit ? 12 : 4);}
                if(pos2 > (nentries2 - 1)) {pos2 = sel2;}
            }
        }

        if(new_pad & BUTTON_LEFT)
        {
            if(FullScreen == 1) new_pad = BUTTON_UP;
            else if (fm_pane == 1)
            {
                if(old_pad & (BUTTON_SELECT | BUTTON_L2 | BUTTON_R2))
                {
                    nentries1 = 0;
                    sprintf(path1, path2);
                    frame = 300; //force immediate refresh
                }

                fm_pane = 0; FullScreen = png_signal = 0;
            }
        }
        else if(new_pad & BUTTON_RIGHT)
        {
            if(FullScreen == 1) new_pad = BUTTON_DOWN;
            else if (fm_pane == 0)
            {
                if(old_pad & (BUTTON_SELECT | BUTTON_L2 | BUTTON_R2))
                {
                    nentries2 = 0;
                    sprintf(path2, path1);
                    frame = 300; //force immediate refresh
                }
                fm_pane = 1; FullScreen = png_signal = 0;
            }
        }

        if(new_pad & BUTTON_UP)
        {
            if(!fm_pane)
            {
                auto_up = 1; if(sel1 > 0) sel1--; else {sel1 = (nentries1 - 1); pos1 = sel1 - (is_vsplit ? 23 : 8);}
                if(sel1 < pos1 + (is_vsplit ? 12 : 4)) pos1--; if(pos1 < 0) pos1 = 0; tick1_move = 1;
            }
            else
            {
                auto_up = 1; if(sel2 > 0) sel2--; else {sel2 = (nentries2 - 1); pos2 = sel2 - (is_vsplit ? 23 : 8);}
                if(sel2 < pos2 + (is_vsplit ? 12 : 4)) pos2--; if(pos2 < 0) pos2 = 0; tick2_move = 1;
            }
        }

        if(new_pad & BUTTON_DOWN)
        {
            if(!fm_pane)
            {
                auto_down = 1;if(sel1 < (nentries1 - 1)) sel1++; else {pos1 = sel1 = 0;}
                if(sel1 > (pos1 + (is_vsplit ? 12 : 4))) pos1++; if(pos1 > (nentries1 - 1)) {pos1 = sel1 = 0;}
                tick1_move = 1;
            }
            else
            {
                auto_down = 1;if(sel2 < (nentries2 - 1)) sel2++; else {pos2 = sel2 = 0;}
                if(sel2 > (pos2 + (is_vsplit ? 12 : 4))) pos2++; if(pos2 > (nentries2 - 1)) {pos2 = sel2 = 0;}
                tick2_move = 1;
            }
        }

        if((FullScreen == 1) && ((new_pad & BUTTON_UP) || (new_pad & BUTTON_DOWN) || (new_pad & BUTTON_L1) || (new_pad & BUTTON_R1)))
        {
            FullScreen = png_signal = 0;
            if(fm_pane == 0)
            {
                char *ext = get_extension(entries1[sel1].d_name);
                if(!(entries1[sel1].d_type & IS_MARKED) && (!strcasecmp(ext, ".jpg") || !strcasecmp(ext, ".png")))
                    new_pad = BUTTON_CROSS_;
            }
            else if (fm_pane == 1)
            {
                char *ext = get_extension(entries2[sel2].d_name);
                if(!(entries2[sel2].d_type & IS_MARKED) && (!strcasecmp(ext, ".jpg") || !strcasecmp(ext, ".png")))
                    new_pad = BUTTON_CROSS_;
            }
        }

        if(((old_pad & BUTTON_L2) && (new_pad & BUTTON_R2)) ||
           ((old_pad & BUTTON_R2) && (new_pad & BUTTON_L2)))
        {
            use_split ^= 1;
            is_vsplit = Video_Resolution.width >= 1280 && use_split != 0;
            sel1 = pos1; sel2 = pos2;
        }


        if(!fm_pane)
        {
            // file_manager pane 0

            if((new_pad & BUTTON_TRIANGLE) && (old_pad & BUTTON_SELECT))
            {
                frame = 300; //force immediate refresh

                if(!strcmp(entries1[sel1].d_name, "..")) n = 0;
                else
                {
                    n = strlen(path1);
                    while(n > 0 && path1[n] != '/') n--;
                }

                if(n == 0) {path1[n] = '/'; path1[n+1] = 0;} else path1[n] = 0;

                is_ntfs = is_ntfs_path(path1);

                if(!is_ntfs && sysLv2FsOpenDir(path1, &fd) == 0)
                    sysLv2FsCloseDir(fd);
                else if(is_ntfs && (pdir = ps3ntfs_diropen(path1)) != NULL)
                    ps3ntfs_dirclose(pdir);
                else
                    path1[1] = 0; // to root

                nentries1 = pos1 = sel1 = 0;
                update_device_sizes |= 1; update_devices1 = true;
            }
            else if(new_pad & BUTTON_CROSS_)
            {
                if (FullScreen == 1)
                {
                    FullScreen = png_signal = 0;
                }
                else if(entries1[sel1].d_type & IS_DIRECTORY)
                {   // change dir
                    if((path1[1] == 0)) update_device_sizes |= 1;

                    for(n = 0; n < MAX_ENTRIES; n++) entries1_type[n] = 0;
                    frame = 300; //force immediate refresh

                    if(!strcmp(entries1[sel1].d_name, ".."))
                    {
                        if(old_pad & BUTTON_SELECT) n = 0;
                        else
                        {
                            n = strlen(path1);
                            while(n > 0 && path1[n] != '/') n--;
                        }

                        if(n == 0) {path1[n] = '/'; strcpy(cur_path1, &path1[n+1]); path1[n+1] = 0;} else {strcpy(cur_path1, &path1[n + 1]); path1[n] = 0;}

                        is_ntfs = is_ntfs_path(path1);

                        if(!is_ntfs && sysLv2FsOpenDir(path1, &fd) == SUCCESS)
                            sysLv2FsCloseDir(fd);
                        else if(is_ntfs && (pdir = ps3ntfs_diropen(path1)) != NULL)
                            ps3ntfs_dirclose(pdir);
                        else
                            path1[1] = 0; // to root

                        nentries1 = 0;
                    }
                    else
                    {
                        n = strlen(path1);
                        if(path1[n - 1] != '/') strcat(path1, "/");
                        strcat(path1, entries1[sel1].d_name);

                        is_ntfs = is_ntfs_path(path1);

                        if(!is_ntfs && use_cobra && (old_pad & BUTTON_SELECT))
                        {
                            if(bAllowNetGames && get_net_status() == SUCCESS)
                            {
                                sprintf(temp_buffer, "http://localhost/mount_ps3%s", path1);
                                char *url = str_replace(temp_buffer, " ", "%20");

                                download_file(url, NULL, 0, NULL);
                                if(url) free(url); url = NULL;

                                if((path2[1] == 0) || strcmp(path2, "/dev_bdvd") == SUCCESS) nentries2 = 0;
                                frame = 300; //force refresh
                            }
                        }

                        if(!is_ntfs && sysLv2FsOpenDir(path1, &fd) == SUCCESS)
                        {
                            nentries1 = 0;
                            sysLv2FsCloseDir(fd);
                        }
                        else if(is_ntfs && (pdir = ps3ntfs_diropen(path1)) != NULL)
                        {
                            nentries1 = 0;
                            ps3ntfs_dirclose(pdir);
                        }
                        else
                            path1[n] = 0;
                    }

                    pos1 = sel1 = 0;
                    update_device_sizes |= 1;
                }
                else
                {
                    char *ext = get_extension(entries1[sel1].d_name);

                    if((use_mamba || use_cobra) && !(entries1[sel1].d_type & IS_MARKED) &&
                           (strcasestr(".mp3|.ogg", ext) != NULL))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);

                        if((snd_inited & INITED_AUDIOPLAYER) && strcmp(audio_file, TEMP_PATH)==0)
                        {
                            StopAudio(); snd_inited &= ~INITED_AUDIOPLAYER;
                        }
                        else
                        {
                            audio_pane = 1;

                            sprintf(audio_file, "%s", TEMP_PATH);
                            if(PlayAudio(audio_file, 0, AUDIO_ONE_TIME)==0) snd_inited|= INITED_AUDIOPLAYER;
                        }
                    }
                    else
                    if((use_mamba || use_cobra) && !(entries1[sel1].d_type & IS_MARKED) && is_audiovideo(ext))
                    {
                        sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/showtime.iso", self_path);
                        sprintf(TEMP_PATH2, "%s/%s", path1, entries1[sel1].d_name);

                        launch_iso_build(TEMP_PATH1, TEMP_PATH2, true);
                    }
                    else if(!(entries1[sel1].d_type & IS_MARKED) && is_audiovideo(ext))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                        launch_video(TEMP_PATH);
                    }
                    else if((use_mamba || use_cobra) && !(entries1[sel1].d_type & IS_MARKED) &&
                           (strcasestr(".iso|.bin|.img|.mdf|.iso.0", ext) != NULL))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                        launch_iso_game(TEMP_PATH, DETECT_EMU_TYPE);
                    }
                    else if(!strcmpext(entries1[sel1].d_name, ".BIN.ENC"))
                    {
                        sprintf(TEMP_PATH1, "%s/%s", path1, entries1[sel1].d_name);
                        sprintf(TEMP_PATH2, "%s", entries1[sel1].d_name);
                        launch_ps2classic(TEMP_PATH1, TEMP_PATH2);
                    }

                    else if(!(entries1[sel1].d_type & IS_MARKED) &&
                            is_retro_file(path1, entries1[sel1].d_name))
                    {
                        char rom_path[MAXPATHLEN];
                        sprintf(rom_path, "%s/%s", path1, entries1[sel1].d_name);
                        launch_retro(rom_path);
                    }
                    else if(!(entries1[sel1].d_type & IS_MARKED) && strcasecmp(ext, ".lua") == SUCCESS)
                    {
                        char lua_path[MAXPATHLEN];
                        sprintf(lua_path, "%s/%s", path1, entries1[sel1].d_name);
                        launch_luaplayer(lua_path);
                    }
                    else if(!(entries1[sel1].d_type & IS_MARKED) && is_browser_file(ext))
                    {
                        if(strcasecmp(ext, ".html") == SUCCESS || strcasecmp(ext, ".htm") == SUCCESS)
                            sprintf(TEMP_PATH, "http://localhost%s/%s", path1, entries1[sel1].d_name);
                        else
                        {
                            sprintf(TEMP_PATH, "%s/USRDIR/temp.txt", self_path);
                            unlink_secure(TEMP_PATH);

                            sprintf(TEMP_PATH, "%s/USRDIR/temp.html", self_path);
                            unlink_secure(TEMP_PATH);

                            FILE *fd;

                            fd = fopen(TEMP_PATH, "w");

                            if(!strcasecmp(ext, ".cfg"))
                            {
                                sprintf(TEMP_PATH1, "%s/%s", path1, entries1[sel1].d_name);
                                sprintf(TEMP_PATH2, "%s/USRDIR/temp.txt", self_path);
                                CopyFile(TEMP_PATH1, TEMP_PATH2);

                                sprintf(temp_buffer, "<body bgcolor=white text=blue leftmargin=0 rightmargin=0><font size=5>%s</font></br><iframe src='http://localhost/%s' border=0 ",
                                        entries1[sel1].d_name, TEMP_PATH1);
                            }
                            else
                                sprintf(temp_buffer, "<body bgcolor=white text=blue leftmargin=0 rightmargin=0><font size=5>%s</font></br><iframe src='http://localhost/%s/%s' border=0 ",
                                        entries1[sel1].d_name, path1, entries1[sel1].d_name);

                            strcat(temp_buffer, "width=100% height=100%></body>");
                            fputs (temp_buffer, fd);
                            fclose(fd);

                            sprintf(TEMP_PATH, "http://localhost/%s/USRDIR/temp.html", self_path);
                        }

                        char* launchargv[1];
                        memset(launchargv, 0, sizeof(launchargv));

                        int len = strlen(temp_buffer);
                        launchargv[0] = (char*)malloc(len + 1); strcpy(launchargv[0], TEMP_PATH);
                        launchargv[1] = NULL;

                        char self[256];
                        sprintf(self, "%s/USRDIR/browser.self", self_path);

                        if(file_exists(self))
                        {
                            fun_exit();
                            SaveGameList();

                            sysProcessExitSpawn2((const char*)self, (char const**)launchargv, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
                        }
                    }

                    else if(!(entries1[sel1].d_type & IS_MARKED) && strcasecmp(ext, ".p3t") == SUCCESS)
                    {
                        sprintf(MEM_MESSAGE, "Do you want to copy %s\nto dev_hdd0/theme folder?", entries1[sel1].d_name);

                        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                        {
                          sprintf(TEMP_PATH1, "%s/%s", path1, entries1[sel1].d_name);
                          sprintf(TEMP_PATH2, "/dev_hdd0/theme/%s", entries1[sel1].d_name);
                          CopyFile(TEMP_PATH1, TEMP_PATH2);

                          sprintf(MEM_MESSAGE, "%s has been copied to the dev_hdd0/theme.", entries1[sel1].d_name);
                          DrawDialogOKTimer(MEM_MESSAGE, 2000.0f);
                        }
                    }

                    else if(!(entries1[sel1].d_type & IS_MARKED) && strcasecmp(ext, ".jpg") == SUCCESS)
                    {
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);

                        if(LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 300; FullScreen = 1;
                        }

                    }
                    else if(!(entries1[sel1].d_type & IS_MARKED) && (strcasecmp(ext, ".png") == SUCCESS || !strcmp(entries1[sel1].d_name, "PS3LOGO.DAT")))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);

                        if(LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 300; FullScreen = 1;
                        }
                    }
                    else if(!options_locked && !(entries1[sel1].d_type & IS_MARKED) && !strcmp(entries1[sel1].d_name, "PARAM.SFO"))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                        if(edit_title_param_sfo(TEMP_PATH) == SUCCESS) exitcode = REFRESH_GAME_LIST;
                    }
                    else if(!options_locked && !(entries1[sel1].d_type & IS_MARKED) && (use_cobra && !use_mamba) && strstr(entries1[sel1].d_name, "webftp_server")!=NULL && (strcasecmp(ext, ".sprx") == SUCCESS))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);

                        bool reboot=false; int size; char *boot_plugins = LoadFile("/dev_hdd0/boot_plugins.txt", &size);
                        unlink_secure("/dev_hdd0/tmp/wm_request");

                        if(size>=36 && strstr(boot_plugins, "/dev_hdd0/plugins/webftp_server.sprx")!=NULL)
                        {
                            if(file_exists("/dev_hdd0/plugins/webftp_server.sprx"))
                            {
                                unlink_secure("/dev_hdd0/plugins/webftp_server.sprx");
                                CopyFile(TEMP_PATH, "/dev_hdd0/webftp_server.sprx"); reboot=true;
                            }
                        }
                        else
                        if(size>=28 && strstr(boot_plugins, "/dev_hdd0/webftp_server.sprx")!=NULL)
                        {
                            sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                            if(file_exists("/dev_hdd0/webftp_server.sprx"))
                            {
                                unlink_secure("/dev_hdd0/webftp_server.sprx");
                                CopyFile(TEMP_PATH, "/dev_hdd0/webftp_server.sprx"); reboot=true;
                            }
                        }

                        if(boot_plugins) free(boot_plugins);
                        if(reboot) sys_reboot();

                    }
                    else if(!options_locked && !(entries1[sel1].d_type & IS_MARKED) && (use_cobra || use_mamba) && (strcasecmp(ext, ".sprx") == SUCCESS))
                    {
                        cobra_unload_vsh_plugin(6);
                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                        cobra_load_vsh_plugin(6, TEMP_PATH, NULL, 0);
                    }
                    else if(!options_locked && (selcount1>1 || !(entries1[sel1].d_type & IS_MARKED)) && strcasecmp(ext, ".pkg") == SUCCESS)
                    {
                        if(old_pad & BUTTON_SELECT)
                        {
                            sprintf(MEM_MESSAGE, "Do you want to mount %s/%s as /dev_bdvd?", path1, entries1[sel1].d_name);

                            if(is_ntfs_path(path1) && DrawDialogYesNo(MEM_MESSAGE) == YES)
                            {
                                sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/pkg.iso", self_path);
                                sprintf(TEMP_PATH2, "%s/%s", path1, entries1[sel1].d_name);

                                unlink_secure(TEMP_PATH1);
                                launch_iso_build(TEMP_PATH1, TEMP_PATH2, false);

                                {fun_exit(); SaveGameList(); exit(0);}
                            }

                            if(!is_ntfs_path(path1))
                            {
                                sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                                hex_editor(HEX_EDIT_FILE, TEMP_PATH, entries1_size[sel1]);
                            }
                            continue;
                        }
                        else if(selcount1 > 1)
                        {
                            for(int r = 0; r < nentries1; r++)
                            {
                                if((entries1[r].d_type & IS_MARKED) && strcasestr(entries1[r].d_name, ".pkg")!=NULL)
                                {
                                    install_pkg(path1, entries1[r].d_name, 0);
                                }
                            }
                            nentries1 = selcount1 = 0; frame = 300; //force immediate refresh
                        }
                        else
                        {
                            install_pkg(path1, entries1[sel1].d_name, 1);

                            sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                            if(file_exists(TEMP_PATH) == false)
                            {
                                nentries1 = 0; sel1--;
                                frame = 300; //force immediate refresh
                            }
                        }
                    }
                    else if(!(entries1[sel1].d_type & IS_MARKED) && strcasecmp(ext, ".self") == SUCCESS)
                    {
                        if((old_pad & BUTTON_SELECT) || is_ntfs_path(path1))
                        {
                            sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                            hex_editor(HEX_EDIT_FILE, TEMP_PATH, entries1_size[sel1]);
                            continue;
                        }
                        else
                        {
                            fun_exit();
                            SaveGameList();

                            sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                            sysProcessExitSpawn2(TEMP_PATH, NULL, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
                            exit(0);
                        }
                    }
                    else if(!options_locked)
                    {
                        sprintf(MEM_MESSAGE, "Do you want to mount %s/%s as /dev_bdvd?", path1, entries1[sel1].d_name);

                        if(is_ntfs_path(path1) && (old_pad & BUTTON_SELECT))
                        {
                            if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                            {
                                sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/pkg.iso", self_path);
                                sprintf(TEMP_PATH2, "%s/%s", path1, entries1[sel1].d_name);

                                int flen = strlen(TEMP_PATH2) - 4;

                                if(flen >= 0 && (strcasestr(".iso|.bin|.mdf|.img|so.0", TEMP_PATH2 + flen) != NULL))
                                    launch_iso_game(TEMP_PATH2, DETECT_EMU_TYPE);
                                else
                                {
                                    unlink_secure(TEMP_PATH1);
                                    launch_iso_build(TEMP_PATH1, TEMP_PATH2, false);
                                }

                                {fun_exit(); SaveGameList(); exit(0);}
                            }
                            continue;
                        }

                        sprintf(TEMP_PATH, "%s/%s", path1, entries1[sel1].d_name);
                        hex_editor(HEX_EDIT_FILE, TEMP_PATH, entries1_size[sel1]);
                        continue;
                    }
                }
            } // cross

            if(!(old_pad & BUTTON_SELECT) && (new_pad & BUTTON_SQUARE))
            {   // select one file/folder
                if((path1[1] != 0) && strcmp(entries1[sel1].d_name, ".."))
                {
                    if(FullScreen && strcasestr(".jpg|.png", get_extension(entries1[sel1].d_name)) != NULL)
                    {
                        sprintf(TEMP_PATH1, "%s/USRDIR/background/PICT8.JPG", self_path);
                        sprintf(TEMP_PATH2, "%s/USRDIR/background/PICT0.JPG", self_path);
                        if(file_exists(TEMP_PATH1) == false) CopyFile(TEMP_PATH2, TEMP_PATH1);

                        sprintf(TEMP_PATH1, "%s/%s", path1, entries1[sel1].d_name);

                        unlink_secure(TEMP_PATH2);
                        CopyFile(TEMP_PATH1, TEMP_PATH2);
                        bk_picture = 3;
                        load_background_picture();
                        break;
                    }
                    else
                    {
                        entries1[sel1].d_type ^= IS_MARKED;
                        if(entries1[sel1].d_type & IS_MARKED)
                        {
                            selcount1++; selsize1 += entries1_size[sel1];
                        }
                        else
                        {
                            selcount1--; selsize1 -= entries1_size[sel1];
                        }
                    }
                }
            }   // square
            else if((old_pad & BUTTON_SELECT) && (new_pad & BUTTON_SQUARE))
            {
                u32 flag = (entries1[sel1].d_type ^ IS_MARKED) & IS_MARKED;

                if((path1[1] != 0))
                {   // select all files/folders
                    selcount1 = 0; selsize1 = 0;

                    for(n = 0; n < nentries1; n++)
                        if(strncmp(entries1[n].d_name, "..", 3))
                        {
                            entries1[n].d_type = (entries1[n].d_type & ~IS_MARKED) | flag;
                            if(entries1[n].d_type & IS_MARKED)
                            {
                                selcount1++; selsize1 += entries1_size[n];
                            }
                        }
                }
                else
                {
                    if(!strncmp((char *) entries1[sel1].d_name, "ntfs", 4) || !strncmp((char *) entries1[sel1].d_name, "ext", 3))
                    {
                        sprintf(MEM_MESSAGE, "Do you want to unmount USB00%i device?", NTFS_Test_Device(entries1[sel1].d_name));

                        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                        {
                            int i = NTFS_Test_Device(entries1[sel1].d_name);

                            if(mounts[i])
                            {   // change to root if unmount the device
                                for (int k = 0; k < mountCount[i]; k++)
                                {
                                    if((mounts[i]+k)->name[0])
                                    {
                                        if(!strncmp(&path1[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) path1[1] = 0;
                                        if(!strncmp(&path2[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) path2[1] = 0;
                                    }
                                }
                            }


                            NTFS_UnMount(i);

                            if((path1[1] == 0)) {path1[1] = nentries1 = pos1 = sel1 = 0; update_device_sizes |= 1; update_devices1 = true;}
                            if((path2[1] == 0)) {path2[1] = nentries2 = pos2 = sel2 = 0; update_device_sizes |= 2; update_devices2 = true;}
                        }
                    }
                }
            } // select+square

            if(new_pad & BUTTON_L3)
            {
                ROT_INC(change_path1, 6, 0);

                nentries1 = pos1 = sel1 = 0;

                frame = 300; //force immediate refresh
                update_device_sizes |= 1;

                switch(change_path1)
                {
                    case 0:
                        if((path1[1] != 0))
                        {
                            strcpy(path1, "/");
                            break;
                        }
                        else
                            change_path1++;
                    case 1:
                        if(strcmp(path1, "/dev_usb000") != SUCCESS && file_exists("/dev_usb000"))
                        {
                            strcpy(path1, "/dev_usb000");
                            break;
                        }
                        else
                            change_path1++;
                    case 2:
                        if(strcmp(path1, "/dev_usb001") != SUCCESS && file_exists("/dev_usb001"))
                        {
                            strcpy(path1, "/dev_usb001");
                            break;
                        }
                        else
                            change_path1++;
                    case 3:
                        if(strcmp(path1, "/dev_usb006") != SUCCESS && file_exists("/dev_usb006"))
                        {
                            strcpy(path1, "/dev_usb006");
                            break;
                        }
                        else
                            change_path1++;
                    case 4:
                        if(strcmp(path1, "/dev_bdvd") != SUCCESS && file_exists("/dev_bdvd"))
                        {
                            strcpy(path1, "/dev_bdvd");
                            break;
                        }
                        else
                            change_path1++;
                    case 5:
                        if(strcmp(path1, self_path) != SUCCESS && file_exists(self_path))
                        {
                            strcpy(path1, self_path);
                            break;
                        }
                        else
                            change_path1++;
                    default:
                        if(strcmp(path1, path2) != SUCCESS && file_exists(path2))
                        {
                            strcpy(path1, path2);
                            break;
                        }
                        else
                            {change_path1 = 0; strcpy(path1, "/");}
                }
            } // l3

            else if(new_pad & BUTTON_R3)
            {
                ROT_INC(change_path1, 6, 0);

                nentries1 = pos1 = sel1 = 0;

                frame = 300; //force immediate refresh
                update_device_sizes |= 1;

                switch(change_path1)
                {
                    case 0:
                        if(strcmp(path1, "/dev_hdd0") != SUCCESS && file_exists("/dev_hdd0"))
                        {
                            strcpy(path1, "/dev_hdd0");
                            break;
                        }
                        else
                            change_path1++;
                    case 1:
                        if(strcmp(path1, "/dev_hdd0/PS3ISO") != SUCCESS && file_exists("/dev_hdd0/PS3ISO"))
                        {
                            strcpy(path1, "/dev_hdd0/PS3ISO");
                            break;
                        }
                        else
                            change_path1++;
                    case 2:
                        if(strcmp(path1, "/dev_hdd0/GAMES") != SUCCESS && file_exists("/dev_hdd0/GAMES"))
                        {
                            strcpy(path1, "/dev_hdd0/GAMES");
                            break;
                        }
                        else
                            change_path1++;
                    case 3:
                        if(strcmp(path1, "/dev_hdd0/game") != SUCCESS && file_exists("/dev_hdd0/game"))
                        {
                            strcpy(path1, "/dev_hdd0/game");
                            break;
                        }
                        else
                            change_path1++;
                    case 4:
                        if(strcmp(path1, "/dev_hdd0/packages") != SUCCESS && file_exists("/dev_hdd0/packages"))
                        {
                            strcpy(path1, "/dev_hdd0/packages");
                            break;
                        }
                        else
                            change_path1++;
                    case 5:
                        if(strcmp(path1, "/dev_hdd0/home") != SUCCESS && file_exists("/dev_hdd0/home"))
                        {
                            strcpy(path1, "/dev_hdd0/home");
                            break;
                        }
                        else
                            change_path1++;
                    default:
                        if(strcmp(path1, path2) != SUCCESS  && file_exists(path2) )
                        {
                            strcpy(path1, path2);
                            break;
                        }
                        else
                            {change_path1 = 0; strcpy(path1, "/dev_hdd0");}
                }
            } // r3
        }

        else
        {
            // file_manager pane 1

            if((new_pad & BUTTON_TRIANGLE) && (old_pad & BUTTON_SELECT))
            {
                frame = 300;

                if(!strcmp(entries2[sel2].d_name, "..")) n = 0;
                else
                {
                    n = strlen(path2);
                    while(n > 0 && path2[n] != '/') n--;
                }

                if(n == 0) {path2[n] = '/'; path2[n+1] = 0;} else path2[n] = 0;

                is_ntfs = is_ntfs_path(path2);

                if(!is_ntfs && sysLv2FsOpenDir(path2, &fd) == 0)
                    sysLv2FsCloseDir(fd);
                else if(is_ntfs && (pdir = ps3ntfs_diropen(path2)) != NULL)
                    ps3ntfs_dirclose(pdir);
                else
                    path2[1] = 0; // to root

                nentries2 = pos2 = sel2 = 0;
                update_device_sizes |= 2; update_devices2 = true;
            }
            else if(new_pad & BUTTON_CROSS_)
            {
                if (FullScreen == 1)
                {
                    FullScreen = png_signal = 0;
                }
                else if(entries2[sel2].d_type & IS_DIRECTORY)
                {   // change dir
                    if((path2[1] == 0)) update_device_sizes |= 2;

                    for(n = 0; n < MAX_ENTRIES; n++) entries2_type[n] = 0;
                    frame = 300; //force immediate refresh

                    if(!strcmp(entries2[sel2].d_name, ".."))
                    {
                        if(old_pad & BUTTON_SELECT) n = 0;
                        else
                        {
                            n = strlen(path2);
                            while(n > 0 && path2[n] != '/') n--;
                        }

                        if(n == 0) {path2[n] = '/'; strcpy(cur_path2, &path2[n+1]); path2[n+1] = 0;} else {strcpy(cur_path2, &path2[n + 1]); path2[n] = 0;}

                        is_ntfs = is_ntfs_path(path2);

                        if(!is_ntfs && sysLv2FsOpenDir(path2, &fd) == SUCCESS)
                            sysLv2FsCloseDir(fd);
                        else if(is_ntfs && (pdir = ps3ntfs_diropen(path2)) != NULL)
                            ps3ntfs_dirclose(pdir);
                        else
                            path2[1] = 0; // to root

                        nentries2 = 0;
                    }
                    else
                    {
                        n = strlen(path2);
                        if(path2[n - 1] != '/') strcat(path2, "/");
                        strcat(path2, entries2[sel2].d_name);

                        is_ntfs = is_ntfs_path(path2);

                        if(!is_ntfs && use_cobra && (old_pad & BUTTON_SELECT))
                        {
                            if(bAllowNetGames && get_net_status() == SUCCESS)
                            {
                                sprintf(temp_buffer, "http://localhost/mount_ps3%s", path2);
                                char *url = str_replace(temp_buffer, " ", "%20");

                                download_file(url, NULL, 0, NULL);
                                if(url) free(url); url = NULL;

                                if((path1[1] == 0) || strcmp(path1, "/dev_bdvd") == SUCCESS) nentries1 = 0;
                                frame = 300; //force refresh
                            }
                        }

                        if(!is_ntfs && sysLv2FsOpenDir(path2, &fd) == SUCCESS)
                        {
                            nentries2 = 0;
                            sysLv2FsCloseDir(fd);
                        }
                        else if(is_ntfs && (pdir = ps3ntfs_diropen(path2)) != NULL)
                        {
                            nentries2 = 0;
                            ps3ntfs_dirclose(pdir);
                        }
                        else
                            path2[n] = 0;
                    }

                    pos2 = sel2 = 0;
                    update_device_sizes |= 2;
                }
                else
                {
                    char *ext = get_extension(entries2[sel2].d_name);

                    if((use_mamba || use_cobra) && !(entries2[sel2].d_type & IS_MARKED) &&
                           (strcasestr(".mp3|.ogg", ext) != NULL))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);

                        if((snd_inited & INITED_AUDIOPLAYER) && strcmp(audio_file, TEMP_PATH)==0)
                        {
                            StopAudio(); snd_inited &= ~INITED_AUDIOPLAYER;
                        }
                        else
                        {
                            audio_pane = 2;

                            sprintf(audio_file, "%s", TEMP_PATH);
                            if(PlayAudio(audio_file, 0, AUDIO_ONE_TIME)==0) snd_inited|= INITED_AUDIOPLAYER;
                        }
                    }
                    else
                    if((use_mamba || use_cobra) && !(entries2[sel2].d_type & IS_MARKED) && is_audiovideo(ext))
                    {
                        sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/showtime.iso", self_path);
                        sprintf(TEMP_PATH2, "%s/%s", path2, entries2[sel2].d_name);

                        launch_iso_build(TEMP_PATH1, TEMP_PATH2, true);
                    }
                    else if(!(entries2[sel2].d_type & IS_MARKED) && is_audiovideo(ext))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                        launch_video(TEMP_PATH);
                    }
                    else if((use_mamba || use_cobra) && !(entries2[sel2].d_type & IS_MARKED) &&
                           (strcasestr(".iso|.bin|.img|.mdf|.iso.0", ext) != NULL))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                        launch_iso_game(TEMP_PATH, DETECT_EMU_TYPE);
                    }
                    else if(!strcmpext(entries2[sel2].d_name, ".BIN.ENC"))
                    {
                        sprintf(TEMP_PATH1, "%s/%s", path2, entries2[sel2].d_name);
                        sprintf(TEMP_PATH2, "%s", entries2[sel2].d_name);
                        launch_ps2classic(TEMP_PATH1, TEMP_PATH2);
                    }

                    else if(!(entries2[sel2].d_type & IS_MARKED) &&
                            is_retro_file(path2, entries2[sel2].d_name))
                    {
                        char rom_path[MAXPATHLEN];
                        sprintf(rom_path, "%s/%s", path2, entries2[sel2].d_name);
                        launch_retro(rom_path);
                    }
                    else if(!(entries2[sel2].d_type & IS_MARKED) && strcasecmp(ext, ".lua") == SUCCESS)
                    {
                        char lua_path[MAXPATHLEN];
                        sprintf(lua_path, "%s/%s", path2, entries2[sel2].d_name);
                        launch_luaplayer(lua_path);
                    }
                    else if(!(entries2[sel2].d_type & IS_MARKED) && is_browser_file(ext))
                    {
                        if(strcasecmp(ext, ".html") == SUCCESS || strcasecmp(ext, ".htm") == SUCCESS)
                            sprintf(TEMP_PATH, "http://localhost%s/%s", path2, entries2[sel2].d_name);
                        else
                        {
                            sprintf(TEMP_PATH, "%s/USRDIR/temp.txt", self_path);
                            unlink_secure(TEMP_PATH);

                            sprintf(TEMP_PATH, "%s/USRDIR/temp.html", self_path);
                            unlink_secure(TEMP_PATH);

                            FILE *fd;

                            fd = fopen(TEMP_PATH, "w");

                            if(!strcasecmp(ext, ".cfg"))
                            {
                                sprintf(TEMP_PATH1, "%s/%s", path2, entries2[sel2].d_name);
                                sprintf(TEMP_PATH2, "%s/USRDIR/temp.txt", self_path);
                                CopyFile(TEMP_PATH1, TEMP_PATH2);

                                sprintf(temp_buffer, "<body bgcolor=white text=blue leftmargin=0 rightmargin=0><font size=5>%s</font></br><iframe src='http://localhost/%s' border=0 ",
                                        entries2[sel2].d_name, TEMP_PATH1);
                            }
                            else
                                sprintf(temp_buffer, "<body bgcolor=white text=blue leftmargin=0 rightmargin=0><font size=5>%s</font></br><iframe src='http://localhost/%s/%s' border=0 ",
                                        entries2[sel2].d_name, path2, entries2[sel2].d_name);

                            strcat(temp_buffer, "width=100% height=100%></body>");
                            fputs (temp_buffer, fd);
                            fclose(fd);

                            sprintf(TEMP_PATH, "http://localhost/%s/USRDIR/temp.html", self_path);
                        }

                        char* launchargv[1];
                        memset(launchargv, 0, sizeof(launchargv));

                        int len = strlen(temp_buffer);
                        launchargv[0] = (char*)malloc(len + 1); strcpy(launchargv[0], TEMP_PATH);
                        launchargv[1] = NULL;

                        char self[256];
                        sprintf(self, "%s/USRDIR/browser.self", self_path);

                        if(file_exists(self))
                        {
                            fun_exit();
                            SaveGameList();

                            sysProcessExitSpawn2((const char*)self, (char const**)launchargv, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
                        }
                    }

                    else if(!(entries2[sel2].d_type & IS_MARKED) && strcasecmp(ext, ".p3t") == SUCCESS)
                    {
                        sprintf(MEM_MESSAGE, "Do you want to copy %s\nto dev_hdd0/theme folder?", entries2[sel2].d_name);

                        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                        {
                          sprintf(TEMP_PATH1, "%s/%s", path2, entries2[sel2].d_name);
                          sprintf(TEMP_PATH2, "/dev_hdd0/theme/%s", entries2[sel2].d_name);
                          CopyFile(TEMP_PATH1, TEMP_PATH2);

                          sprintf(MEM_MESSAGE, "%s has been copied to the dev_hdd0/theme.", entries2[sel2].d_name);
                          DrawDialogOKTimer(MEM_MESSAGE, 2000.0f);
                        }
                    }

                    else if(!(entries2[sel2].d_type & IS_MARKED) && strcasecmp(ext, ".jpg") == SUCCESS)
                    {
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);

                        if(LoadTextureJPG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 300; FullScreen = 1;
                        }

                    }
                    else if(!(entries2[sel2].d_type & IS_MARKED) && (strcasecmp(ext, ".png") == SUCCESS || !strcmp(entries2[sel2].d_name, "PS3LOGO.DAT")))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);

                        if(LoadTexturePNG(TEMP_PATH, TEMP_PICT) == SUCCESS)
                        {
                            png_signal = 300; FullScreen = 1;
                        }
                    }
                    else if(!options_locked && !(entries2[sel2].d_type & IS_MARKED) && !strcmp(entries2[sel2].d_name, "PARAM.SFO"))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                        if(edit_title_param_sfo(TEMP_PATH) == SUCCESS) exitcode = REFRESH_GAME_LIST;
                    }
                    else if(!options_locked && !(entries2[sel2].d_type & IS_MARKED) && (use_cobra && !use_mamba) && strstr(entries2[sel2].d_name, "webftp_server")!=NULL && (strcasecmp(ext, ".sprx") == SUCCESS))
                    {
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);

                        bool reboot=false; int size; char *boot_plugins = LoadFile("/dev_hdd0/boot_plugins.txt", &size);
                        unlink_secure("/dev_hdd0/tmp/wm_request");

                        if(size>=36 && strstr(boot_plugins, "/dev_hdd0/plugins/webftp_server.sprx")!=NULL)
                        {
                            if(file_exists("/dev_hdd0/plugins/webftp_server.sprx"))
                            {
                                unlink_secure("/dev_hdd0/plugins/webftp_server.sprx");
                                CopyFile(TEMP_PATH, "/dev_hdd0/webftp_server.sprx"); reboot=true;
                            }
                        }
                        else
                        if(size>=28 && strstr(boot_plugins, "/dev_hdd0/webftp_server.sprx")!=NULL)
                        {
                            sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                            if(file_exists("/dev_hdd0/webftp_server.sprx"))
                            {
                                unlink_secure("/dev_hdd0/webftp_server.sprx");
                                CopyFile(TEMP_PATH, "/dev_hdd0/webftp_server.sprx"); reboot=true;
                            }
                        }

                        if(boot_plugins) free(boot_plugins);
                        if(reboot) sys_reboot();

                    }
                    else if(!options_locked && !(entries2[sel2].d_type & IS_MARKED) && (use_cobra || use_mamba) && (strcasecmp(ext, ".sprx") == SUCCESS))
                    {
                        cobra_unload_vsh_plugin(6);
                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                        cobra_load_vsh_plugin(6, TEMP_PATH, NULL, 0);
                    }
                    else if(!options_locked && (selcount2>1 || !(entries2[sel2].d_type & IS_MARKED)) && strcasecmp(ext, ".pkg") == SUCCESS)
                    {
                        if(old_pad & BUTTON_SELECT)
                        {
                            sprintf(MEM_MESSAGE, "Do you want to mount %s/%s as /dev_bdvd?", path2, entries2[sel2].d_name);

                            if(is_ntfs_path(path2) && DrawDialogYesNo(MEM_MESSAGE) == YES)
                            {
                                sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/pkg.iso", self_path);
                                sprintf(TEMP_PATH2, "%s/%s", path2, entries2[sel2].d_name);

                                unlink_secure(TEMP_PATH1);
                                launch_iso_build(TEMP_PATH1, TEMP_PATH2, false);

                                {fun_exit(); SaveGameList(); exit(0);}
                            }

                            if(!is_ntfs_path(path2))
                            {
                                sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                                hex_editor(HEX_EDIT_FILE, TEMP_PATH, entries2_size[sel2]);
                            }
                            continue;
                        }
                        else if(selcount2 > 1)
                        {
                            for(int r = 0; r < nentries2; r++)
                            {
                                if((entries2[r].d_type & IS_MARKED) && strcasestr(entries2[r].d_name, ".pkg")!=NULL)
                                {
                                    install_pkg(path2, entries2[r].d_name, 0);
                                }
                            }
                            nentries2 = selcount2 = 0; frame = 300; //force immediate refresh
                        }
                        else
                        {
                            install_pkg(path2, entries2[sel2].d_name, 1);

                            sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                            if(file_exists(TEMP_PATH) == false)
                            {
                                nentries2 = 0; sel2--;
                                frame = 300; //force immediate refresh
                            }
                        }
                    }
                    else if(!(entries2[sel2].d_type & IS_MARKED) && strcasecmp(ext, ".self") == SUCCESS)
                    {
                        if((old_pad & BUTTON_SELECT) || is_ntfs_path(path2))
                        {
                            sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                            hex_editor(HEX_EDIT_FILE, TEMP_PATH, entries2_size[sel2]);
                            continue;
                        }
                        else
                        {
                            fun_exit();
                            SaveGameList();

                            sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                            sysProcessExitSpawn2(TEMP_PATH, NULL, NULL, NULL, 0, 3071, SYS_PROCESS_SPAWN_STACK_SIZE_1M);
                            exit(0);
                        }
                    }
                    else if(!options_locked)
                    {
                        sprintf(MEM_MESSAGE, "Do you want to mount %s/%s as /dev_bdvd?", path2, entries2[sel2].d_name);

                        if(is_ntfs_path(path2) && (old_pad & BUTTON_SELECT))
                        {
                            if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                            {
                                sprintf(TEMP_PATH1, "%s/USRDIR/TEMP/pkg.iso", self_path);
                                sprintf(TEMP_PATH2, "%s/%s", path2, entries2[sel2].d_name);

                                int flen = strlen(TEMP_PATH2) - 4;

                                if(flen >= 0 && (strcasestr(".iso|.bin|.mdf|.img", TEMP_PATH2 + flen) != NULL))
                                    launch_iso_game(TEMP_PATH2, DETECT_EMU_TYPE);
                                else
                                {
                                    unlink_secure(TEMP_PATH1);
                                    launch_iso_build(TEMP_PATH1, TEMP_PATH2, false);
                                }

                                {fun_exit(); SaveGameList(); exit(0);}
                            }
                            continue;
                        }

                        sprintf(TEMP_PATH, "%s/%s", path2, entries2[sel2].d_name);
                        hex_editor(HEX_EDIT_FILE, TEMP_PATH, entries2_size[sel2]);
                        continue;
                    }
                }
            } // cross

            if(!(old_pad & BUTTON_SELECT) && (new_pad & BUTTON_SQUARE))
            {   // select one file/folder
                if((path2[1] != 0) && strcmp(entries2[sel2].d_name, ".."))
                {
                    if(FullScreen && strcasestr(".jpg|.png", get_extension(entries2[sel2].d_name)) != NULL)
                    {
                        sprintf(TEMP_PATH1, "%s/USRDIR/background/PICT8.JPG", self_path);
                        sprintf(TEMP_PATH2, "%s/USRDIR/background/PICT0.JPG", self_path);
                        if(file_exists(TEMP_PATH1) == false) CopyFile(TEMP_PATH2, TEMP_PATH1);

                        sprintf(TEMP_PATH1, "%s/%s", path2, entries2[sel2].d_name);

                        unlink_secure(TEMP_PATH2);
                        CopyFile(TEMP_PATH1, TEMP_PATH2);
                        bk_picture = 3;
                        load_background_picture();
                        break;
                    }
                    else
                    {
                        entries2[sel2].d_type ^= IS_MARKED;
                        if(entries2[sel2].d_type & IS_MARKED)
                        {
                            selcount2++; selsize2 += entries2_size[sel2];
                        }
                        else
                        {
                            selcount2--; selsize2 -= entries2_size[sel2];
                        }
                    }
                }
            }   // square
            else if((old_pad & BUTTON_SELECT) && (new_pad & BUTTON_SQUARE))
            {
                u32 flag = (entries2[sel2].d_type ^ IS_MARKED) & IS_MARKED;

                if((path2[1] != 0))
                {   // select all files/folders
                    selcount2 = 0; selsize2 = 0;

                    for(n = 0; n < nentries2; n++)
                        if(strncmp(entries2[n].d_name, "..", 3))
                        {
                            entries2[n].d_type = (entries2[n].d_type & ~IS_MARKED) | flag;
                            if(entries2[n].d_type & IS_MARKED)
                            {
                                selcount2++; selsize2 += entries2_size[n];
                            }
                        }
                }
                else
                {
                    if(!strncmp((char *) entries2[sel2].d_name, "ntfs", 4) || !strncmp((char *) entries2[sel2].d_name, "ext", 3))
                    {
                        sprintf(MEM_MESSAGE, "Do you want to unmount USB00%i device?", NTFS_Test_Device(entries2[sel2].d_name));

                        if(DrawDialogYesNo(MEM_MESSAGE) == YES)
                        {
                            int i = NTFS_Test_Device(entries2[sel2].d_name);

                            if(mounts[i])
                            {   // change to root if unmount the device
                                for (int k = 0; k < mountCount[i]; k++)
                                {
                                    if((mounts[i]+k)->name[0])
                                    {
                                        if(!strncmp(&path1[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) path1[1] = 0;
                                        if(!strncmp(&path2[1], (mounts[i]+k)->name, 5 - ((mounts[i]+k)->name[0] == 'e'))) path2[1] = 0;
                                    }
                                }
                            }


                            NTFS_UnMount(i);

                            if((path1[1] == 0)) {path1[1] = nentries1 = pos1 = sel1 = 0; update_device_sizes |= 1; update_devices1 = true;}
                            if((path2[1] == 0)) {path2[1] = nentries2 = pos2 = sel2 = 0; update_device_sizes |= 2; update_devices2 = true;}
                        }
                    }
                }

            } // select+square

            if(new_pad & BUTTON_L3)
            {
                ROT_INC(change_path2, 6, 0);

                nentries2 = pos2 = sel2 = 0;
                frame = 300; //force immediate refresh
                update_device_sizes |= 2;

                switch(change_path2)
                {
                    case 0:
                        if((path2[1] != 0))
                        {
                            strcpy(path2, "/");
                            break;
                        }
                        else
                            change_path2++;
                    case 1:
                        if(strcmp(path2, "/dev_usb000") != SUCCESS && file_exists("/dev_usb000"))
                        {
                            strcpy(path2, "/dev_usb000");
                            break;
                        }
                        else
                            change_path2++;
                    case 2:
                        if(strcmp(path2, "/dev_usb001") != SUCCESS && file_exists("/dev_usb001"))
                        {
                            strcpy(path2, "/dev_usb001");
                            break;
                        }
                        else
                            change_path2++;
                    case 3:
                        if(strcmp(path2, "/dev_usb006") != SUCCESS && file_exists("/dev_usb006"))
                        {
                            strcpy(path2, "/dev_usb006");
                            break;
                        }
                        else
                            change_path2++;
                    case 4:
                        if(strcmp(path2, "/dev_bdvd") != SUCCESS && file_exists("/dev_bdvd"))
                        {
                            strcpy(path2, "/dev_bdvd");
                            break;
                        }
                        else
                            change_path2++;
                    case 5:
                        if(strcmp(path2, self_path) != SUCCESS && file_exists(self_path))
                        {
                            strcpy(path2, self_path);
                            break;
                        }
                        else
                            change_path2++;
                    default:
                        if(strcmp(path2, path1) != SUCCESS && file_exists(path1))
                        {
                            strcpy(path2, path1);
                            break;
                        }
                        else
                            {change_path2 = 0; strcpy(path2, "/");}
                }
            } // l3

            else if(new_pad & BUTTON_R3)
            {
                ROT_INC(change_path2, 6, 0);

                nentries2 = pos2 = sel2 = 0;
                frame = 300; //force immediate refresh
                update_device_sizes |= 2;

                switch(change_path2)
                {
                    case 0:
                        if(strcmp(path2, "/dev_hdd0") != SUCCESS && file_exists("/dev_hdd0"))
                        {
                            strcpy(path2, "/dev_hdd0");
                            break;
                        }
                        else
                            change_path2++;
                    case 1:
                        if(strcmp(path2, "/dev_hdd0/PS3ISO") != SUCCESS && file_exists("/dev_hdd0/PS3ISO"))
                        {
                            strcpy(path2, "/dev_hdd0/PS3ISO");
                            break;
                        }
                        else
                            change_path2++;
                    case 2:
                        if(strcmp(path2, "/dev_hdd0/GAMES") != SUCCESS && file_exists("/dev_hdd0/GAMES"))
                        {
                            strcpy(path2, "/dev_hdd0/GAMES");
                            break;
                        }
                        else
                            change_path2++;
                    case 3:
                        if(strcmp(path2, "/dev_hdd0/game") != SUCCESS && file_exists("/dev_hdd0/game"))
                        {
                            strcpy(path2, "/dev_hdd0/game");
                            break;
                        }
                        else
                            change_path2++;
                    case 4:
                        if(strcmp(path2, "/dev_hdd0/packages") != SUCCESS && file_exists("/dev_hdd0/packages"))
                        {
                            strcpy(path2, "/dev_hdd0/packages");
                            break;
                        }
                        else
                            change_path2++;
                    case 5:
                        if(strcmp(path2, "/dev_hdd0/home") != SUCCESS && file_exists("/dev_hdd0/home"))
                        {
                            strcpy(path2, "/dev_hdd0/home");
                            break;
                        }
                        else
                            change_path2++;
                    default:
                        if(strcmp(path2, path1) != SUCCESS  && file_exists(path1) )
                        {
                            strcpy(path2, path1);
                            break;
                        }
                        else
                            {change_path2 = 0; strcpy(path2, "/dev_hdd0");}
                }

            } // r3
        }
        }// set menu

        sysUtilCheckCallback();
        test_audio_file(false);
    }

    if(copy_mem) free(copy_mem); copy_mem = NULL;

    sprintf(TEMP_PATH, "%s/%s", self_path, "/config/path1.bin");
    SaveFile(TEMP_PATH, (char *)path1, MAX_PATH_LEN);
    sprintf(TEMP_PATH, "%s/%s", self_path, "/config/path2.bin");
    SaveFile(TEMP_PATH, (char *)path2, MAX_PATH_LEN);

    return exitcode;
}
#endif