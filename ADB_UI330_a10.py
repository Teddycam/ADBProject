"""
    This program is a "Swiss knife for mobile Android devices testing and throughputting using Android
    Debug Bridge (ADB) that should be installed to c:\adb directory before program execution.
    Note:
    On the testing Android device Developer mode and USB debug should be enabled!

    Author: Mikhail Sokolov, Megafon Lab
"""
import os
import sys
import signal
import csv
import re
import logging
import paramiko
import telnetlib
import time
import subprocess
from subprocess import Popen, PIPE, STDOUT
import threading
from threading import Event, Lock, Thread, Timer
from PyQt5 import QtCore, QtGui, QtWidgets
from PyQt5.QtCore import QRegExp, QStringListModel, Qt, QTimer
from PyQt5.QtGui import QRegExpValidator, QFont
from PyQt5.QtWidgets import QWidget, QPushButton, QToolTip, QVBoxLayout, QListView, QAbstractItemView

#######################
# Constants definition
#######################

TO_REM_1 = '\r\nNo MOTD has been set\r\n\n'             # telnet pattern
TO_REM_2 = '\r\n\n'                                     # telnet pattern
UNKNOWN_VALUE = '2147483647'                            # Android's 'N/A'
PARAM_1 = 'shell  dumpsys telephony.registry |grep '    # for ADB data inflating without ""
PARAM_1a = 'shell  "dumpsys telephony.registry |grep '  # for ADB data inflating with ""
PARAM_1b = 'shell "dumpsys wifiscanner |awk '           # for ADB data inflating with awk pattern
PARAM_1c = 'shell "dumpsys wifi | grep mWifiInfo"'      # for ADB WiFi data inflating to devdata[0]['wRSSI']
PARAM_2 = ['mServiceState',                             # for ADB data inflating (from telephony.registry service)
           'mSignalStrength',
           'mCellInfo',
           'mPreciseDataConnectionState',
           'mPhoneCapability',
           'mBarringInfo']

# Initial Ports values:
DEF_IPERF_PORT = 5000 # used for iperf3, for iperf2_tcp +10, for iperf2_udp+20
IPERF3_PORT    = 5000 # Default, integer, not str! (== DEF_IPERF_PORT)
IPERF2_PORT_TCP = 5010 # Default ( if not in the configuration and not changed manually via IPERF3_PORT value +10)
IPERF2_PORT_UDP = 5020 # Default ( if not in the configuration and not changed manually via IPERF3_PORT value +20)
TIMEOUT_IPERF_CLIENT = 3 # Default watchdog timeout for iperf client in seconds

##########################
# Variables initialization
##########################
procdata = [[],] * 15                                      # array of returned ADB strings with required data
'''
    procdata[0]         - 'mServiceState'
    procdata[1]         - 'mSignalStrength'
    procdata[2]         - 'mCellInfo'
    procdata[3]         - 'mPreciseDataConnectionState'
    procdata[4]         - 'mPhoneCapability'
    procdata[5]         - 'mBarringInfo'
    procdata[6]         - 'shell ip a'
    procdata[7][0]      - 'shell dumpsys wifi | grep mWifiInfo"'   (wifi signal, speed etc.)
    procdata[7][1]      - 'shell dumpsys wifi' (wifi status)
    procdata[8]         - 'c:\adb\adb.exe shell df /storage/emulated' (disk status)
    procdata[9]         - 'shell dumpsys battery' (battery info)
    procdata[10]        - 'shell free -h' (memory status#1)
    procdata[11]        - 'shell cat /proc/meminfo' (memory status#2)
    procdata[12]        - 'shell vmstat' (memory status#3)
    procdata[13]        - 'shell top -n1' (memory status#4)
'''
nr_support = 'is NOT supported'                         # initial value
DevModel = ''                                           # initial value
Device_SN = ''                                           # initial value
SDK_ver  = ''                                           # initial value <-- getprop ro.build.version.sdk
sim_state = ''                                          # initial value <-- getprop gsm.sim.state
abi_list = ''                                           # initial value of supported abi list (armeabi-v7a, arm64-v8a, x86 etc.)
iphonesubinfo_registers = []                            # array of answers to registers 0..29
imei = [None,None]                                           # for IMEI
imsi = [None,None]                                           # for IMSI
isdn = [None,None]                                           # for MSISDNs
Measonly = False                                        # flag for inflating meas data only for speed up process
idxnr = -1                                               # initial value of idx
pkglst = ''                                             # initial list of pkgs in the pkg (iperf) directory
apklst = ''                                             # initial list of apk in the apk directory
SignalStrength = []                                     # initial Signal strength data
tip = '10.88.128.52'                                    # default ip address for telnet Att
tprt = 3001                                             # default port value for telnet Att
attipstr = None                                         # initial ip address for telnet Att
attchn = None                                           # initial port value for telnet Att
SS = []                                                 # SignalStrength per RadioModule
sss = []                                                # SS splitted to values for Androids ver <10
ip = []                                                 # IP addresses with UP interfaces
mip = ''                                                # mobile IP addresses with UP interfaces
mmtu = ''                                               # MTU of the UP mobile itf
wip = ''                                                # WiFi IP addresses with UP interfaces
mif = ''                                                # rmnet UP interface name
wif = ''                                                # WiFi  UP interface name
RMq = 0                                                 # initial quantity of Radio Modules
sshipstr = ''                                           # initial ip addr str of Attenuator
atconn = False                                          # initial state
att_chnl_lst = ''                                       # initial Att. channels list which attenuate the DUT connection
watchdog_timer_expired = False                          # initial value (signal from watchdog to GUI)
# Настройка  модуля Paramiko
client_look_for_keys = True
client_timeout = 5000
sshconn = False

fn = "adb_config.csv"                      # filename for csv file with iperf settings and ssh servers list
servers = ['----;--------;---;---']        # initial servers list where [0] is IP, [1] is server name,
                                           # [2] = username, [3] = password
servers_csv_count = 0                      # initial value of quantity of records in csv file

# default iperf parameters, may be overwritten by values from the config file (if exist):
iperf2_version = 'iperf2.1.4'
iperf3_version = 'iperf3.7'
iperf3_srvr_params  = '-s -D '            # default TCP iperf3 server params (universal for tcp/udp)
iperf2_srvr_tcp_params  = '-s -D -w16M '   # default TCP iperf2 server params
iperf2_srvr_udp_params  = '-s -D -u ' # default UDP iperf2 server params
iperf_srvr_cmd2chk = 'iperf'               # for check at kill process
torun = 'c:\\adb\\adb.exe '                # ADB path
iperf_clnt_path  = '/data/local/tmp/'
iperf_clnt_path2 = '/data/local/tmp/'
iperf3_tcp0 = ' -i1 -w400K  -O2 '
iperf3_udp0 = ' -u -i1 -O2 '
iperf2_tcp0 = ' -i1 -w16M '
iperf2_udp0 = ' -u -i1 '

""" Android (up to version 9) signal strength data structures:
 public String toString() {
    return ("SignalStrength:"
1            + " " + mGsmSignalStrength   mSS
2            + " " + mGsmBitErrorRate	    BER

3            + " " + mCdmaDbm		        RSSI
4            + " " + mCdmaEcio            ECIO

5            + " " + mEvdoDbm		        RSSI
6            + " " + mEvdoEcio	        ECIO
7            + " " + mEvdoSnr		        SINR

8            + " " + mLteSignalStrength   SS
9            + " " + mLteRsrp		        RSRP
10            + " " + mLteRsrq	        RSRQ
11            + " " + mLteRssnr	        SINR*10
12            + " " + mLteCqi             CQI

13            + " " + (isGsm ? "gsm|lte" : "cdma"));
"""

LEVELS = ['mSS', 'BER', 'EcNo', 'RSCP', 'SNR', 'ECIO', 'RSSI', 'RSRP', 'RSRQ', 'SINR', 'CQI',
          'ssRsrp', 'ssRsrq', 'ssSinr'] # devdata dict keys for signal levels

# data structure (dict) of devdata per Radio Module
datastr = {'mRegCS': None, 'mRegPS': None, 'mCNOp': None,
           'mCSRT': None, 'mPSRT': None, 'mPLMN': None, 'mRATC': None,
           'mConn': None, 'mAPN': None,
           'mChan': None, 'mBW': None, 'RTech': None,
           'mSS': None, 'BER': None,
           'EcNo': None, 'RSCP': None, 'SNR': None,
           'ECIO': None, 'RSSI': None,
           'RSRP': None, 'RSRQ': None, 'SINR': None, 'CQI': None,
           'ssRsrp': None, 'ssRsrq': None, 'ssSinr': None,
           'mIF': None, 'mIP': None, 'mMTU': None,
           'WiFiConn': None, 'wIF': None, 'wIP': None,
           'WiFi_SSID': None, 'WiFi_Generation': None,'wRSSI': None,
           'WiFi_link_speed': None, 'WiFi_TX_link_speed': None, 'WiFi_RX_link_speed': None}

devdata = []  # array of results per each SIM/RadioModule in the datastr dict format
NetOps = []
ServStates = ''
WiFiScanData = ['']
dAtt = 0                             # Required Attenuation correction
PKG_DIR = 'c:\\adb\\install\\iperf'  # pkg directory
APK_DIR = 'c:\\adb\\install\\apk'    # apk directory
Liperfsrvrs = []                     # found iperf executables at the SSH server to select which shoul be runned
L_iperfsrvrs_versions = []           # it's versions list
iperf_srvr_to_run = ''               # selected iperf executables to run as daemon servers
Lpkg = []                            # founded pkg in pkg directory
L_pkg_sel = []                       # selected pkg list for installation (global)
Lapk = []                            # founded apk in apk directory
L_apk_sel = []                       # selected apk list for installation (global)
Liperfs = []                         # founded iperf instances at SSH server
L_iperfs_sel = []                    # selected iperf instances list to be killed(global)

########################
#    GUI vars & const
########################
lst_l1 = ['']
lst_l2 = ['']
tv1_lst1 = []
tv1_lst2 = []
tv1_lst3 = []
tv2_lst1 = []
tv2_lst2 = []
tv2_lst3 = []


########################################################################
# COMMON functions
########################################################################

# class Watchdog2(Exception):
#     def __init__(self, *args):
#         if args:
#             self.message = args[0]
#         else:
#             self.message = None
#     def str(selfself):
#         print('calling str')
#         if self.message:
#             return 'Watchdog2, {0}'.format(self.message)
#         else:
#             return 'Watchdog2 raised'

def colored_text(txt, col_val='#000000', weight=400):
    '''Coloring text using CSS format #rrggbb'''
    cText = f"<span style=\"  font-weight:{weight}; color:{col_val};\" >"
    cText += txt + "</span>"
    return cText

def valfrombrackets(inputstr):
    """ извлечение числа/строки из строчного значения в скобках вида (25)
    This for parse something
    :param inputstr: str
    :return: string value without brackets
    e.g. inputstr = '(la la)'
    return = 'la la'
    """
    pos01 = inputstr.find("(")
    pos02 = inputstr.find(")")
    if pos01 >= 0 and pos02 > 0:
        return inputstr[pos01 + 1:pos02]
    else:
        logger.error('ValFromBrackets cannot find any value in %s:', inputstr)
        logger.error('Returned None')
        return None

def kill_iperf_clients(ver=2):
    ''' Derive process id of the runned iperf/ipef3 at Android device and kill it'''
    iperf_v = iperf2_version if ver == 2 else iperf3_version
    logger.info(f'---------------: called kill_iperf_client iperf version:{iperf_v}' )
    s = torun + 'shell pidof '+ iperf_v
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    if p.returncode > 0:
        logger.debug('---------------: Error: ' + p.stderr)
        logger.debug('---------------: Output: ' + p.stdout)
        logging.debug("pidof doesn't work")
        return "pidof doesn't work"
    else:
        pid = p.stdout.replace('\n','')
        pids = re.findall(r'\d+',pid)
        logger.debug(f'PIDs found:{pids}')
        killresult = True
        if len(pids)>0:
            for pid in pids:
                logger.debug(f'processing PID:{pid}')
                s = f'{torun} shell "kill -s 1 {pid}"' # send to pid sig#1 Hangup(HUP)
                p = (subprocess.run(s, capture_output=True, text=True, shell=True))
                print(f'>{s}')
                if (p.returncode > 0 or p.stdout):
                    logger.debug('---------------: Error: ' + p.stderr)
                    logger.debug('---------------: Output: ' + p.stdout)
                    killresult = False
                    logging.debug(f'kill PID:{pid} NOK, returncode:{p.returncode}, out = {p.stdout}')
                else:
                    print(f'PID:{pid} successfully killed:{p.stdout}')
                    killresult = killresult and True
                    logging.debug(f'PID:{pid} successfully killed')
        if killresult:
            return 'killed'
        else:
            return f'cannot kill OR bad PID:{pid} or process already finished'

class Watchdog(Exception):
    def __init__(self, timeout_parm=TIMEOUT_IPERF_CLIENT, userHandler=None):  # timeout in seconds
        self.timeout = timeout_parm
        self.handler = userHandler if userHandler is not None else self.defaultHandler
        self.timer = Timer(self.timeout, self.handler)
        self.timer.start()

    def reset(self):
        self.timer.cancel()
        self.timer = Timer(self.timeout, self.handler)
        self.timer.start()

    def stop(self):
        self.timer.cancel()

    def defaultHandler(self):
        global watchdog_timer_expired
        thr_res_kill_iperfs_clients = threading.Thread(target = kill_iperf_clients, args=(2,)).start()
        watchdog_timer_expired = True
        # ADB_App_Main.periodic_iperf_client_timeout(self)
        # kill_iperf_clients(2)
        # raise subprocess.TimeoutExpired(torun, TIMEOUT_IPERF_CLIENT)  # Watchdog2
        # raise IOError("watchdog2")  # Watchdog2





def get_state(Key):
    """ translate Service State for Androids ver. <10 from int value
    This for translating Service State for Androids ver. <10 from int value
       0 --> IN_SERVICE
       1 --> OUT_OF_SERVICE
       2 --> EMERGENCY_ONLY
       3 --> POWER_OFF
    :param Key: this is str Key for data with Key separator, for example 'RSSI:' or "SINR="
    :return: str translated Service State
    e.g. key = '0'
    return = 'IN_SERVICE'
    """
    states = ['IN_SERVICE', 'OUT_OF_SERVICE', 'EMERGENCY_ONLY', 'POWER_OFF']
    if Key in ['0', '1', '2', '3']:
        return states[int(Key)]
    else:
        return None


# извлечение значения из строки по ключу
def get_value_from_string(inputstr, Key, Sep):
    """
    This for getting something value from text db by it's Key
    :param inputstr:str this is input string with required data to be inflated from
    :param Key:str this is str Key for data with Key separator, for example 'RSSI:' or "SINR="
    :param Sep:str string with data separator (' ' or ','  or ';' or '\n' etc.)
    :return: str data from text db
    e.g. inputstr = 'mLte=CellSignalStrengthLte:
                    rssi=-57 rsrp=-86 rsrq=-11 rssnr=260 cqi=2147483647 ta=2147483647 miuiLevel=5 level=4'
         key = 'rssi='
         sep = ' '
    return = -57
    """
    unknownValue = '2147483647'
    posKey = inputstr.find(Key)  # точка начала Key в строке
    posSep = inputstr[posKey + len(Key):].find(Sep)  # точка начала sep за искомым значенем от конца Key
    if posKey >= 0 and posSep >= 0:  # -1  означает не найдено

        # от конца Key до начала sep за искомым значенем
        if inputstr[posKey + len(Key):posKey + len(Key) + posSep] != unknownValue:
            val = inputstr[posKey + len(Key):posKey + len(Key) + posSep]
        else:
            val = None
    else:
        val = None
    return val


def get_att_chnl_lst_from_input(input: str) -> list:
    """AI is creating summary for get_att_chnl_lst_from_input
    Args:
        input (str): [description]
    Return:
        list of att. channels :str(int) or None if error input
    """
    att_chnl_list_int = []
    if ',' in input:
        res1 = re.findall(r'\d+', input)
        if ('-' in input or
            ':' in input):
            for i in range(int(res1[0]), int(res1[1]) + 1):
                att_chnl_list_int.append(str(i))
            if len(res1) > 2:
                for i in range(2, len(res1)):
                    att_chnl_list_int.append(res1[i])
        else:
            for each in res1:
                if (int(each) > 0 and int(each) < 25):
                    att_chnl_list_int.append(each)
                else:
                    return None
        return att_chnl_list_int
    elif (':' in input or
          '-' in input):
        res1 = re.findall(r'\d+', input)
        if len(res1) == 2:
            if (int(res1[0]) < 25 and
               int(res1[0]) > 0 and
               int(res1[1]) < 25 and
               int(res1[1]) > 0):
                for i in range(int(res1[0]), int(res1[1]) + 1):
                    att_chnl_list_int.append(str(i))
                return att_chnl_list_int
            else:
                return None
        elif len(res1) == 1:
            if (int(res1[0]) > 0 and
               int(res1[0]) < 25):
                att_chnl_list_int.append(res1[0])
                return att_chnl_list_int
        else:
            return None
    else:
        res1 = re.findall(r'\d+', input)
        if len(res1) > 2:
            for each in res1:
                att_chnl_list_int.append(int(each))
            return att_chnl_list_int
        elif len(res1) == 2:
            for i in range(int(res1[0]), int(res1[1]) + 1):
                att_chnl_list_int.append(str(i))
            return att_chnl_list_int
        elif len(res1) == 1:
            att_chnl_list_int.append(res1[0])
            return att_chnl_list_int
        else:
            return None

########################################################################
# MAIN functions & procedures
########################################################################


def connect_ssh(ip: str, port: str, uname: str, pwd: str):
    """ Connect to  SSH server with ip:port under {Uname:pwd}
    Args:
        ip (str): ssh server IP
        port (str): SSH port (22)
        uname (str): User name
        pwd (str): User password
    Returns:
        (Bool): SSHconnection state
    """
    global sshconn, sshclient
    logger.debug('---------------: call ConnectSSH at server ' + ip + ':' + port)
    if not sshclient:
        sshclient = paramiko.SSHClient()
        sshclient.load_system_host_keys()
        sshclient.set_missing_host_key_policy(paramiko.AutoAddPolicy())
        logger.debug('---------------: sshclient reactivated')
    else:
        logger.debug('---------------: sshclient active')
    try:
        sshclient.connect(ip, int(port), username=uname, password=pwd,
                      look_for_keys=client_look_for_keys, timeout=client_timeout)
    except:
        logger.debug('Log in was not successfull, try again with correct credentials')
        sshclient.close()
        sshconn = False
        return sshconn
    if sshclient:
        sshconn = True
    return sshconn


def disconnect_ssh():
    """ Disconnect from  SSH server with ip:port under Uname:pwd
        +++ and may be, kill latest iperf server process (???)
    Args:
    Returns:
        (Bool): SSHconnection state
        global sshconn, sshclient
    """
    global sshconn, sshclient
    logger.debug('---------------: call DisconnectSSH from server ')
    global sshconn, sshclient
    p = []
    if sshclient and sshconn:
        [p1, e1] = exec_linux_command('exit')
        sshclient.close()
        p.append('> exit')
        p.extend(p1)
        p.extend(e1)
    sshconn = False
    return p


def exec_linux_command(cmd: str):
    """ Execute SSH cmnd on the server with ip:port under 
    Args:
        cmd (str): SSH comand
    Returns:
        [[str],str]: stdout.splitlines, stderr.readlines
    """
    logger.debug('---------------: call ExecLinuxcmd ' + cmd)
    if sshclient and sshconn:
        ssh_in, ssh_out, ssh_err = sshclient.exec_command(cmd)
        # while True:
        #     out = (ssh_stdout.readline()) #.decode('utf-8'))
        #     if ssh_stdout.channel.exit_status_ready():
        #         break
        # out = ssh_stdout.readline() #.decode('utf-8') # readlines(), read().splitlines()
        # out = ssh_stdout.readlines() 
        out = ssh_out.readlines()
        err = ssh_err.readlines()
        return out, err
    else:
        logger.debug('---------------: SSH connection lost')
        return '> ' + cmd, 'SSH connection lost'
    # return out, err


def exec_linux_command_from_SU(cmd: str, pwd: str):
    """ Execute SSH "su cmd" on the server with ip:port under {Uname:pwd} with additional request of SU pwd 

    Args:
        pwd (str): User password == User (sudoer) password
        cmd (str): SSH comand (without su)

    Returns:
        [[str],str]: stdout.splitlines, stderr.readlines
    """
    logger.debug('---------------: call ExecSULinuxcmd: su ' + cmd)
    if sshclient and sshconn:
        ssh_stdin, ssh_stdout, ssh_stderr = sshclient.exec_command('sudo -S ' + cmd)
        ssh_stdin.write(pwd + '\n')
        ssh_stdin.flush()
        out = ssh_stdout.read().decode('utf-8').splitlines()
        err = ssh_stderr.readlines()
        return out, err
    else:
        logger.debug('---------------: SSH connection lost')
        return '', 'SSH connection lost'


def exec_su(pwd: str):
    """ Execute SU  cmd gor switvhing user to root 
    Args:
        pwd (str): User password == sudoer password
    Returns:
        [[str],str]: stdout.splitlines, stderr.readlines
    """
    logger.debug('---------------: call ExecSU ')
    if sshclient and sshconn:
        ssh_stdin, ssh_stdout, ssh_stderr = sshclient.exec_command('su')
        ssh_stdin.write(pwd + '\n')
        ssh_stdin.flush()
        out = ssh_stdout.read().decode('utf-8').splitlines()
        err = ssh_stderr.readlines()
        return out, err
    else:
        logger.debug('---------------: SSH connection lost')
        return '', 'SSH connection lost'


def check_ssh_Connect():
    """ for checking SSH connection with ssh_ip:ssh_port server under {sshusr|sshpwd}
    Returns:
        Bool: Successfully checked (True) or not (False)
    """
    p = ['> uname']
    logger.debug('---------------: call check_ssh_Connect')
    if sshclient and sshconn:
        [p1, e1] = exec_linux_command('uname')
        for s in e1:
            p.append(s)
        for s in p1:
            p.append(s)
            if 'Linux' in s:  # if b'Linux'... if std.out wo decode
                return True, p
        logger.error('Linux command was not executed')
        return False, p
    else:
        logger.error('SSH connection lost')
        return False, 'SSH connection lost'


def SSH_check_ping(ping_ip: str):
    """for ping ping_ip from the SSH server
    Args:
        ping_ip (_type_): ping IP adress 
    Returns:
        Bool: Successfully checked (True) or not (False)
    """
    logger.debug('---------------: call SSH_check_ping from server ' + ' to ' + ping_ip)
    [p, e] = exec_linux_command('ping -c 1 ' + ping_ip)
    for i in range(len(p)):
        if 'packets transmitted,' in p[i]:
            result = re.findall(r'\d+', p[i])
            if (result[1] == result[0] and  # received packets == sent packets
               result[2] == '0'):          # % lost packets == 0
                return True
            else:
                return False


def check_self_ping_to(ping_ip: str):
    """check ping from the PC where script is executed
    Args:
        ping_ip (_type_): ping IP adress
    Returns:
        Bool: Successfully checked (True) or not (False)
    """
    # logger.debug('---------------: call check_self_ping from the PC ' + ' to ' + ping_ip)
    p1 = subprocess.Popen('ping -n 1 -w 999 ' + ping_ip, stdin=PIPE, stdout=PIPE, stderr=PIPE,
        shell=True, encoding='CP866')
    p = p1.stdout.readlines()
    for i in range(len(p)):
        logger.info(p[i])
        if ('packets transmitted,' in p[i] or
            'Пакетов: отправлено' in p[i] or
            'Packets: Sent' in p[i]):
            result = re.findall(r'\d+', p[i])
            if (result[1] == result[0] and  # received packets == sent packets
                    result[2] == '0'):  # % lost packets == 0
                return True
            else:
                return False


def clear_att_answer(ans1: str):
    """for clearing input string from some text and symbols

    Args:
        ans1 (str): String to be cleared

    Returns:
        (str): cleared string
    """
    ans2 = ans1.replace(TO_REM_1, '')
    ans = ans2.replace(TO_REM_2, '')
    result = re.findall(r'\d+', ans)
    if len(result) > 0:
        return str(int(result[1]))
    else:
        return str(-1)


def to_bytes(line):
    """for decoding input string from bytes str to utf-8 str
    Args:
        line (str): String to be cleared
    Returns:
        (str): cleared string
    """
    return f"{line}\n".encode("utf-8")


def exec_telnet_command(ip, port, cmd):
    """Execute cmd via telnet of ip:port remote host
    Args:
        ip (str): IP address for telnet connection
        port (_type_): port of telnet connection
        cmd (_type_): command to be sent via telnet
    Returns:
        (str)): answer from remote host to telnet command 
    """
    tn = telnetlib.Telnet(ip, port)
    tn.read_until(b'Connection Open', timeout=3)
    tn.write(cmd)
    time.sleep(0.2)
    ttt = tn.read_very_eager().decode('ascii')
    tn.close()
    return ttt


def read_str_value_from_attenuator_channel(ip, Att: int):
    """to read attenuation value of selected Attenuator channel #Att 
    Args:
        ip : str = IP address of attenuator
        Att :int (Attenuator channel)
    Returns:
        (str): att. value in dB | None if no answer
    """
    logger.debug('---------------: read_str_value_from_attenuator_channel() ' + ' to ' + ip + ' + channel#' + str(Att))
    if (Att > 0 and
       Att < 25):
        command = to_bytes('RA' + str(Att))
        answer = clear_att_answer(exec_telnet_command(ip, tprt, command))
    else:
        answer = None
    return answer


def set_attenuator_channel_str_value_with_check(ip, Att: int, value: int):
    """to set attenuation value of selected Attenuator channel with checking (reading new value)
    Args:
        ip: str = Att IP
        Att: int = Attenuator channel#
        value: int = Attenuator new value
    Returns:
        (str): att. value in dB | None if no answer
    """
    if (Att > 0 and
       Att < 25 and
       value >= 0 and
       value < 64):
        command = to_bytes('SA -R ' + str(Att) + " " + str(value))
        answer = clear_att_answer(exec_telnet_command(ip, tprt, command))
        logger.debug('---------------: call set_attenuator_channel_str_value_with_check() IP: ' + ip
                     +' channel #' + str(Att) + ' to  value = ' + str(value) + 'dB '
                     + 'Returned:' + str(answer) +'dB')
    else:
        answer = None
    return answer


def set_attenuator_channel_str_value_without_read(ip: int, Att: int, value: int):
    """to set attenuation value of selected Attenuator channel without reading new value
    Args:
        ip: str = Att IP
        Att: int = Attenuator channel#
        value: int = Attenuator new value
    Returns:
        (str): att. value in dB | None if no answer
    """
    if (Att > 0 and
       Att < 25 and
       value >= 0 and
       value < 64):
        command = to_bytes('SA ' + str(Att) + " " + str(value))
        answer = clear_att_answer(exec_telnet_command(ip, tprt, command))
        logger.debug('---------------: call set_attenuator_channel_str_value_without_read() channel#' + Att
                     + ' to  value = ' + str(value) + 'dB ' + 'Returned:' + answer +'dB')
    else:
        answer = None
    return answer


def check_attenuator_connect(ip, port):
    """for check Attenuator ipaddr:port connection 
    Args:
        ip (str): Telnet Ip address of Attenuator
        port (int): Telnet port of Attenuator
    Returns:
        (Bool): checked OK (True) or NOK (False)
    """
    command = to_bytes('IDN')
    answer = exec_telnet_command(ip, port, command)  # clearans()
    if '50PA-846' in answer:
        checkedOK = True
    else:
        checkedOK = False
    return checkedOK


def get_iperf_instances_from_server(iperf_srvr_cmd: str):
    """_summary_ to invoke processes of runned iperf instanses from SSH server
    Args:
        iperf_srvr_cmd: str
    Return:
        p: [] list of instances
    """
    global Liperfs
    logger.debug('---------------: call getIperfInstances')
    Liperfs = []  # clear list of instances
    p = []        # ssh log list
    sshcmd = 'ps -eaf |grep iperf'   # iperf_srvr_cmd+'"'
    [p1, e1] = exec_linux_command(sshcmd)
    if len(e1) == 0:
        p.append('> ' + sshcmd + '\n')  # log cmd
        logger.debug('---------------: Liperfs:')
        for s in p1:
            logger.debug('---------------: ' + str(s))  # Liperfs item, filter it:
            if ('grep' not in s and
               'bash' not in s and
               s != ''):
                Liperfs.append(str(s))
        p.extend(p1)
        p.extend(e1)
    else:
        logger.debug('---------------: Error: ' + str(p1))
        logger.debug('---------------: Output: ' + str(e1))
    logger.debug('---------------: Liperfs: ' + str(p1))
    return p


def get_pids_from_ps_cmd_return(s: str):
    """_summary_ to invoke pid from ps -eaf string for iperf instance kill
    Args:
        s: str string from 
    Return:
        Liperfs global [] list of iperf instances
    """
    p = []  # log list
    logger.debug('---------------: call getPIDfromStr from:' + str(s))
    if iperf_srvr_cmd2chk in s:
        proc = re.findall(r'\d+', s)
        return proc[0]
    else:
        return None


def kill_iperf_instance(pid: str,pwd):
    """
    Kill received process id
    :param pid: process id
    : pwd: str SU password
    :return: res (Bool)
             p (list(str)) = operation log
    """
    logger.debug('---------------: call kill_Iperf_instance process id: ' + str(pid))
    p = []
    [p1, e1] = exec_linux_command_from_SU('kill ' + str(pid), pwd)  # ============>kill iperf
    p.append('> kill ' + str(pid) + '\n')
    p.extend(p1)
    p.extend(e1)
    if len(e1) == 0:
        res = True
    else:
        res = False
    return res, p


def run_iperf_server(iperf_srvr_name, iperf_srvr_params, iperfport: int):
    """_summary_
    Args:
        iperf_srvr_name (str): 'iperf'|'iperf3'|'/local/bin/iperf3.10.1' etc: version ==path to run it on server
        iperf_srvr_params (str): '-s -D -p', for example
        iperfport (int):
        port to listening, 5201 default, script use ports 5300 (iperf2 DL)/5400(iperf2 UL) /5500 (iperf3)
    Returns:
        to_kill, (Bool) 
        to_rerun, (Bool)
        p:        [''] log records
    """

    def run_iperf_cmd(cmd):
        """
        Internal function for iperf run
        :param cmd:str ssh iperf command
        :return: p:list (logfile)
        :return: to_rerun, to_kill: Bool - flags
        """
        logger.debug('------------: call run_iperf_cmd ' + cmd)
        to_rerun = False
        to_kill = False
        p = ['>' + cmd]  # internal log
        [p1, e1] = exec_linux_command(cmd)  # =====================>
        logger.debug('---------------: In: ' + cmd)
        logger.debug('---------------: Out: ')
        p.append(p1)
        logger.debug('---------------: ' + str(p1))
        logger.debug('---------------: Err: ')
        for se in e1:
            p.append(se)
            logger.debug('---------------: ' + str(se))
            if 'Address already in use' in se:  # iperf should be restarted
                to_rerun = True
            elif 'invalid option' in se:  # iperf not started
                to_rerun = True
            elif 'Running Iperf Server as a daemon' in se:  # iperf started OK
                to_kill = False
                to_rerun = False
        return to_kill, to_rerun, p

# check chosen iperf version
    p = []  # list with log strings
    ssh_cmd = iperf_srvr_name.replace('\n', '') + ' -v'  # check chosen iperf version
    (to_kill1, to_rerun1, p1) = run_iperf_cmd(ssh_cmd)  # =====================> run iperf
    p.extend(p1)
# run chosen iperf version in server mode as a Daemon
#     ssh_cmd = iperf_srvr_name + ' ' + iperf_srvr_params + ' -p ' + str(iperfport)
    ssh_cmd = f'{iperf_srvr_name} {iperf_srvr_params} -p {str(iperfport)}'
    logger.debug(f'------------: call run_iperfsrvr:  {ssh_cmd}')
    (to_kill, to_rerun, p1) = run_iperf_cmd(ssh_cmd)  # =====================> run iperf
    p.extend(p1)
    to_kill = to_kill or to_kill1
    to_rerun = to_rerun or to_rerun1
    return to_kill, to_rerun, p


def attenuator_channel_value_change_main(ip, attchn: str, dAtt: int):
    """ to change attenuation of the selected Att and channel, if possible to +-dAtt (dB )
    Args:
        ip: str = Att.IP
        attchn: str = Att channel
        dAtt: int = +- delta value to be att changed
    Returns:
        result(str): ( text result of the attenuation)
    """
    p = []  # Att.log
    nA = 0  # initial value
    logger.debug('---------------: call attchange_main() IP: '+ ip + 'channel#'+ str(attchn)
                 + ' to ' + str(dAtt) + 'dB')

    # connect to the attenuator
    # read channel att.value
    # if possible,change Att to dAtt and return ' Attenuation successfully changed to dAtt dB,
    # now in Att IP Ch# Att = xx dB'
    # if not possible, return "Attenuation cannot be changed to dAtt dB due to <>, now in Att IP Ch# Att = xx dB"

    if ((attipstr and
       attchn) and
       check_attenuator_connect(attipstr, tprt)):
        cA = read_str_value_from_attenuator_channel(attipstr, int(attchn))
        if cA:
            curAtt = int(cA)
            if (curAtt + dAtt >= 0 and curAtt + dAtt < 64):  # check required attenuation set possibility
                nA = set_attenuator_channel_str_value_with_check(attipstr, int(attchn), curAtt + dAtt)
            else:
                return ('Attenuation CANNOT be changed to ' + str(curAtt + dAtt) + ' dB. Now at Att. '
                        + str(attipstr) + '  Ch. ' + str(attchn) + ' Attenuation = ' + cA + ' dB')
            if nA:
                # newAtt = int(nA)
                return ('Attenuation successfully changed to ' + str(dAtt) + ' dB. Now at Att. '
                        + str(attipstr) + '  Ch. ' + str(attchn) + ' Attenuation = ' + nA + ' dB')
            else:
                return 'CANNOT set Attenuation = ' + str(curAtt + dAtt) + ' dB.'
        else:
            return 'CANNOT read Attenuator'
    else:
        return 'CANNOT connect. Please, connect to the attenuator first!'


class CreateIperfsListToRun(QtWidgets.QDialog):
    """
    Display list of iperf versions at the servers to select version to be started
    Args:
        Liperfsrvrs: list of found iperfs (global)
    Returns:
        self.iperfsrvrs2run(list(str)): selected iperfs to be started
    """
    def __init__(self):
        super().__init__()
        self.setupUI()

    def setupUI(self):
        """
        setup UI for the CreateIperfsListToRun
        :return: L_iperfsrvrs2run
        """
        self.res = []  # result
        self.p = []  # log
        self.to_rerun = False
        logger.debug('---------------: CreateIperfsListToRun.setupUI:')
        Liperfsrvrs_with_ver = []
        wn = QWidget(self)
        self.setWindowTitle("Select Iperf to run as server mode daemon")
        self.resize(400, 400)
        self.view = QListView()
        self.view.setSelectionMode(QAbstractItemView.MultiSelection)
        logger.debug('---------------: ' + str())
        if len(L_iperfsrvrs_versions) == len(Liperfsrvrs):
            for i in range(len(Liperfsrvrs)):
                Liperfsrvrs_with_ver.append(Liperfsrvrs[i] + ' '*(40-len(Liperfsrvrs[i])) + 'ver.' + L_iperfsrvrs_versions[i])
            model = QStringListModel(Liperfsrvrs_with_ver)
        else:
            model = QStringListModel(Liperfsrvrs)
        self.setFont(QFont("Consolas",9))
        self.view.setModel(model)
        box = QVBoxLayout(self)
        box.addWidget(self.view)
        button = QPushButton("Select iperf to run as server mode daemons")
        button.clicked.connect(self.create_iperfs_list_to_run_on_clicked)
        self.iperfsrvrs2run = iperf_srvr_to_run  # = sel.data().replace('\n', '')
        box.addWidget(button)
        self.setLayout(box)
        self.show()

    def convert_List_with_ver_to_List_without_ver(self):
        ''' remove version information from the iperfs to be runned
        L_iperfsrvrs2run
        :return: L_iperfsrvrs2run withot version info via temporary iperfsrvrs3run list
        '''
        global iperf_srvr_to_run
        a = iperf_srvr_to_run.find('ver.')
        if a > 0:
            s = iperf_srvr_to_run[:a - len('ver.')].replace(' ', '')
        else:
            s = iperf_srvr_to_run
        print(iperf_srvr_to_run)
        iperf_srvr_to_run = s
        print(iperf_srvr_to_run)


    def create_iperfs_list_to_run_on_clicked(self):
        """ to select on server iperf executables to run its
        Input:
            L_iperfsrvrs2run (global)
        Returns:
            type_: str # 
            description: str # operation result string
        """
        global iperf_srvr_to_run, IPERF2_PORT_TCP, IPERF2_PORT_UDP  # selected iperf executables to run as daemon servers
        logger.debug('---------------: ListIperfsToRun_on_clicked:')
        IPERF2_PORT_TCP = IPERF3_PORT + 10
        IPERF2_PORT_UDP = IPERF3_PORT + 20
        for sel in self.view.selectedIndexes():
            iperf_srvr_to_run = str(sel.data())  # selected items
            self.convert_List_with_ver_to_List_without_ver()
            logger.debug('-------------->: sel.data() = ' + str(sel.data()))
            if 'iperf3' in iperf_srvr_to_run:
                [to_kill, to_rerun, p1] = run_iperf_server(iperf_srvr_to_run,
                                                           iperf3_srvr_params, IPERF3_PORT) # iperf3 tcp + udp
                self.p.extend(p1)
                logger.debug('-------------->: iperf server run: ' + iperf_srvr_to_run)
                if to_rerun:
                    self.res.append(f'iperf server  {iperf_srvr_to_run} cannot be runned, kill it and re-run!')
                    self.to_rerun = True
                else:
                    self.res.append(f'iperf server  {iperf_srvr_to_run} successfully runned')
            elif ('iperf' in iperf_srvr_to_run and
                  not 'iperf3' in iperf_srvr_to_run): # iperf2
                [to_kill, to_rerun, p1] = run_iperf_server(iperf_srvr_to_run.replace('\n', ''),
                                                           iperf2_srvr_tcp_params, IPERF2_PORT_TCP) # iperf2 tcp
                self.p.extend(p1)
                if to_rerun:
                    self.res.append(f'iperf server  {iperf_srvr_to_run} cannot be runned, kill it and re-run!')
                    self.to_rerun = True
                else:
                    self.res.append(f'iperf server  {iperf_srvr_to_run} successfully runned')
                [to_kill, to_rerun, p1] = run_iperf_server(iperf_srvr_to_run.replace('\n', ''),
                                                           iperf2_srvr_udp_params, IPERF2_PORT_UDP) # iperf2 udp
                self.p.extend(p1)
                logger.debug('-------------->: iperf server run: ' + iperf_srvr_to_run)
                if to_rerun:
                    self.res.append(f'iperf server  {iperf_srvr_to_run} cannot be runned, kill it and re-run!')
                    self.to_rerun = True
                else:
                    self.res.append(f'iperf server  {iperf_srvr_to_run} successfully runned')
            else:
                logger.debug('-------------->: Nothing to run for {L_iperfsrvrs2run}')
            # self.convert_List_with_ver_to_List_without_ver
            super().accept()


class CreateIperfsListToKill(QtWidgets.QDialog):
    def __init__(self):
        super().__init__()
        self.setupUI()

    def setupUI(self):
        self.res = []  # result
        self.to_rerun = False
        self.p = []  # log
        logger.debug('---------------: CreateIperfsListToKill.setupUI:')
        wndw = QWidget(self)
        self.setWindowTitle("Select executed Iperf instance(s) to kill")
        self.resize(600, 400)
        self.view = QListView()
        self.view.setSelectionMode(QAbstractItemView.MultiSelection)  # QtWidgets.QAbstractItemView.MultiSelection
        logger.debug('---------------: ' + str(Liperfs))
        model = QStringListModel(Liperfs)
        self.setFont(QFont("Consolas",9))
        self.view.setModel(model)
        box = QVBoxLayout(self)
        box.addWidget(self.view)
        button = QPushButton("Kill selected iperf instances")
        button.clicked.connect(self.create_iperfs_list_to_kill_on_clicked)
        self.L_iperfs_sel = L_iperfs_sel  # = sel.data()
        box.addWidget(button)
        self.setLayout(box)
        self.show()

    def create_iperfs_list_to_kill_on_clicked(self):
        """ to select on server selected iperf instances to kill its
        Returns:
            type_: str # 
            description: str # operation result string
        """
        global L_iperfs_sel  # selected iperf instances list to be killed
        logger.debug('---------------: ListIperfsToKill_on_clicked:')
        for sel in self.view.selectedIndexes():
            L_iperfs_sel = str(sel.data())  # one of selected items
            logger.debug('-------------->: sel.data() = ' + str(sel.data()))
            pid = get_pids_from_ps_cmd_return(L_iperfs_sel)  # process id invoke from string
            if pid:
                logger.info('---------------: pid to kill it: ' + pid)
                [killres, p1] = kill_iperf_instance(pid, sshpwd)
                self.p.extend(p1)
                if killres:
                    logger.debug('-------------->: process killed: ' + pid)
                    self.res.append('process ' + pid + ' successfully killed')
                else:
                    logger.debug('-------------->: process NOT killed: ' + pid)
                    self.res.append('process ' + pid + ' was not killed')
            super().accept()


class CreateListPkg2Install(QtWidgets.QDialog):
    def __init__(self):
        super().__init__()
        self.setupUI()

    def setupUI(self):
        self.res = []
        logger.debug('---------------: CreateListPkg2Install.setupUI:')
        window = QWidget(self)
        self.setWindowTitle("Select packages to be installed")
        self.resize(400, 400)
        self.view = QListView()
        self.view.setSelectionMode(QAbstractItemView.MultiSelection)  # QtWidgets.QAbstractItemView.MultiSelection
        logger.debug('---------------: ' + str(Lpkg))
        model = QStringListModel(Lpkg)
        self.view.setModel(model)
        box = QVBoxLayout(self)
        box.addWidget(self.view)
        button = QPushButton("Remove ALL installed AND install selected packages")
        button.clicked.connect(self.create_list_pkg_to_install_on_clicked)
        self.L_pkg_sel = L_pkg_sel  # = sel.data()
        box.addWidget(button)
        self.setLayout(box)
        self.show()

    def create_list_pkg_to_install_on_clicked(self):
        """_summary_ to install into device selected packages
        Returns:
            _type_: str
            _description_  operation result string
        """
        global L_pgk_sel
        logger.debug('---------------: Listpkg2install_on_clicked:')
        if remove_all_packages():
            logger.debug('-------------->: All of packages on device successfully removed')
        else:
            logger.debug('-------------->: Packages cannot be removed')

        wnd = QtWidgets.QWidget()                                                     # new window for widget
        wnd.setWindowTitle("Класс QProgressDialog")                                   # Tittle
        wnd.resize(300, 70)                                                           # Size
        # wnd.show()                                                                  # not required to be showed
        dialog = QtWidgets.QProgressDialog("APK unstallation", "&Cancel", 0, 20, wnd)  # QProgressDialog for new window
        dialog.setWindowTitle("APK installation progress")                            # Tittle
        # dialog.setModal(True)                                                       #
        i2 = 0                                                                        # Current progress in %%
        dialog.show()                                                                 # show progressbar dialog
        dialog.resize(300, 100)                                                       # progressbar size
        imax = len(self.view.selectedIndexes())                                       # Quantity of selected apks
        dialog.setRange(0, imax)                                                      # set progress range from 0 to
                                                                                      # max # of selected apks
        dialog.setValue(i2)                                                           # set current progress

        dialog.setLabelText('Chosen apk(s) installation: ' + str(i2) + ' of ' + str(imax))  # label: current proc

        for sel in self.view.selectedIndexes():
            QtWidgets.qApp.processEvents()                                            # events processing
            L_pkg_sel = str(sel.data())  # list of selected items
            logger.debug('-------------->: sel.data() = ' + str(sel.data()))
            pkgname = os.path.basename(L_pkg_sel)

            dialog.setLabelText('Wait: ' + pkgname + ' installation...')                # label: current proc
            QtWidgets.qApp.processEvents()                                              # events processing
            if dialog.wasCanceled():                                                    # check Cancel pressed
                break                                                                   # break apk installation
                                                                                        # cycle if cancelled

            logger.info('---------------: selected PKG for installation: ' + pkgname)
            if install_single_package(L_pkg_sel):
                logger.debug('-------------->: Installed: ' + pkgname)
                self.res.append('pkg ' + pkgname + ' successfully installed')
            else:
                logger.debug('-------------->: Not installed: ' + pkgname)
                self.res.append('pkg ' + pkgname + ' is not installed')
            super().accept()


class CreateAPKsList2Install(QtWidgets.QDialog):
    def __init__(self):
        super().__init__()
        self.setupUI()

    def setupUI(self):
        self.res = []  # список выбранных apk для установки
        logger.debug('---------------: CreateAPKsList2Install.setupUI:')
        window = QWidget(self)
        self.setWindowTitle("Select applications to be installed, check installation permissions!")
        self.resize(480, 400)
        self.view = QListView()
        self.view.setSelectionMode(QAbstractItemView.MultiSelection)  # QtWidgets.QAbstractItemView.MultiSelection
        logger.debug('---------------: ' + str(Lapk))
        model = QStringListModel(Lapk)
        self.view.setModel(model)
        box = QVBoxLayout(self)
        box.addWidget(self.view)
        button = QPushButton("Install selected apk.")
        button.clicked.connect(self.create_apks_list_to_install_on_clicked)
        self.L_apk_sel = L_apk_sel  # = sel.data()
        box.addWidget(button)
        self.setLayout(box)
        self.show()

    def create_apks_list_to_install_on_clicked(self):
        """_summary_ to install into device selected .apk files
        Returns:
            _type_: str
            _description_  operation result string
        """
        global L_apk_sel
        logger.debug('---------------: Listapk2install_on_clicked:')

        wnd = QtWidgets.QWidget()                                                      # new window for widget
        wnd.setWindowTitle("Класс QProgressDialog")                                    # Tittle
        wnd.resize(300, 70)                                                            # Size
        # wnd.show()                                                                   # not required to be showed
        dialog = QtWidgets.QProgressDialog("APK unstallation", "&Cancel", 0, 20, wnd)  # QProgressDialog for new window
        dialog.setWindowTitle("APK installation progress")                             # Tittle
        # dialog.setModal(True)                                                        #
        i2 = 0                                                                         # Current progress in %%
        dialog.show()                                                                  # show progressbar dialog
        dialog.resize(300, 100)                                                        # progressbar size
        imax = len(self.view.selectedIndexes())                                        # Quantity of selected apks
        dialog.setRange(0, imax)                                                       # set progress range from 0
                                                                                       # to max # of selected apks
        dialog.setValue(i2)                                                            # set current progress

        dialog.setLabelText('Chosen apk(s) installation: ' + str(i2) + ' of ' + str(imax))   # label: current proc
        for sel in self.view.selectedIndexes():  # for each selected apk
            QtWidgets.qApp.processEvents()                                             # events processing
            L_apk_sel = str(sel.data())         # fill selected apk list
            logger.debug('-------------->: sel.data() = ' + str(sel.data()))
            apkname = os.path.basename(L_apk_sel)
            i = apkname.find('_')               # слева направо !!
            if i > 0:
                apkname = apkname[:i]

            dialog.setLabelText('Wait: ' + apkname + ' installation...')  # label: current proc
            QtWidgets.qApp.processEvents()                                              # events processing
            if dialog.wasCanceled():                                                    # check Cancel pressed
                break                                                                   # break apk installation cycle
                                                                                        # if cancelled
            logger.info('---------------: selected APK for installation: ' + apkname)
            apkres = install_single_apk(L_apk_sel)
            i2 += 1                                                                     # increment progress
            dialog.setValue(i2)                                                         # set current progress

            if 'Success' in apkres:
                logger.debug('-------------->: Installed: ' + apkname)
                self.res.append('apk ' + apkname + ' : ' + apkres)
            else:
                logger.debug('-------------->: Not installed: ' + apkname + apkres)
                self.res.append('apk ' + apkname + ' not installed:' + apkres)

        super().accept()
        dialog.close()                                                                  # close progress bar when
                                                                                        # installation finished


def remove_all_packages():
    '''
        Remove all of installed tmp pkgs at the device
        Input: none
        Output: result (Bool) mean Success or not
    '''
    # 
    s = torun + 'shell rm /data/local/tmp/*'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    logger.debug('---------------: adb command: ' + s)
    logger.debug('---------------: RetCode: ' + str(p.returncode))
    if p.returncode > 0:
        logger.debug('---------------: Error: ' + p.stderr)
        logger.debug('---------------: Output: ' + p.stdout)
        return False
    else:
        return True


def install_single_package(pkgpath: str):
    '''
        Install single pkg file to the device
        Input: pkgpath = local drive:\\path\\filename (str)
        Output: result (Bool) mean Success or not
    '''
    global pkglst
    logger.debug('---------------: Installation pkg: ' + pkgpath)
    pkgname = os.path.basename(pkgpath)
    
    # Copy pkg to /data/local/tmp:
    s = torun + 'push ' + pkgpath + ' /data/local/tmp'
    p = subprocess.run(s, capture_output=True, text=True, shell=True)
    logger.debug('---------------: adb command: ' + s)
    logger.debug('---------------: RetCode: ' + str(p.returncode))
    if p.returncode > 0:
        logger.debug('---------------: Push Error: ' + p.stderr)
        logger.debug('---------------: Push Output: ' + p.stdout)
    s = torun + 'shell chmod 777 /data/local/tmp/' + pkgname  # to add execution permission!
    p = subprocess.run(s, capture_output=True, text=True, shell=True)
    if p.returncode > 0:
        logger.debug('---------------: Chmod Error: ' + p.stderr)
        logger.debug('---------------: Chmod Output: ' + p.stdout)
    # read directory, check that installed pkg filename is present:
    s = torun + 'shell ls -l /data/local/tmp'
    p = subprocess.run(s, capture_output=True, text=True, shell=True)
    logger.debug('---------------: adb command: ' + s)
    logger.debug('---------------: RetCode: ' + str(p.returncode))
    if p.returncode > 0:
        logger.debug('---------------: Error: ' + p.stderr)
        logger.debug('---------------: Output: ' + p.stdout)
    pkglst = p.stdout
    result = pkgname in p.stdout
    return result


def install_single_apk(apkpath: str):
    '''
        Install single apk file to the device
        Input: apkpath = local drive:\\path\\filename.apk (str)
        Output: result/answer (str) for installed apk
    '''
    logger.debug(f'---------------: Installation apk: {apkpath}')

    # Install single apk to the device via ADB:
    s = torun + 'install -r ' + apkpath
    p = subprocess.run(s, capture_output=True, text=True, shell=True)
    logger.debug('---------------: adb command: ' + s)
    logger.debug('---------------: RetCode: ' + str(p.returncode))
    apkres = p.stdout
    apkname = os.path.basename(apkpath)
    if (p.returncode == 0 or
            'Success' in p.stdout):
        logger.debug('---------------: Output: ' + apkres + ' for ' + apkname)
    else:
        logger.debug('---------------: APK installation error: ' + str(p.stderr))
        logger.debug('---------------: Output: ' + apkres)
    return apkres


def get_apk_list():
    ''' Get list of all installed apk from DUT
        Output: apklst == list of all installed apk (str)
    '''

    # get list of installed apks, check that installed apk is installed:
    s = torun + 'shell pm list packages'
    p = subprocess.run(s, capture_output=True, text=True, shell=True)
    logger.debug('---------------: adb command: ' + s)
    logger.debug('---------------: RetCode: ' + str(p.returncode))
    if p.returncode > 0:
        logger.debug('---------------: Error: ' + p.stderr)
        logger.debug('---------------: Output: ' + p.stdout)
    apklst = p.stdout
    return apklst

############################################################################################
# Main. Functions()


def prepare_packages_list_main():
    """_summary_ Find all files in the pkg (iperf) install directory, store its names
    in the global pkg list var "Lpkg" of str
       Return: global str var Lpkg
    """
    global Lpkg
    Lpkg = []
    logger.debug('---------------: Prepare_pkg_lst_main:')
    files_pkg = os.listdir(PKG_DIR)
    for j in range(len(files_pkg)):
        Lpkg.append(PKG_DIR + '\\' + files_pkg[j])
        logger.debug('--------------<: ' + PKG_DIR + '\\' + files_pkg[j])
    # return


def prepare_apk_list_main():
    """_summary_ Find all files in the apk install directory, store its names in the global pkg list var "Lapk" of str
       Return: global str var Lapk (apk in dir), 
               global apklst (installed apk on DUT)
    """
    global Lapk
    global apklst
    Lapk = []
    logger.debug('---------------: Prepare_apk_lst_main:')
    apklst = get_apk_list()
    files_apk = os.listdir(APK_DIR)
    for j in range(len(files_apk)):
        Lapk.append(APK_DIR + '\\' + files_apk[j])
        logger.debug('--------------<: ' + APK_DIR + '\\' + files_apk[j])
    # return


############################################################################################
# Main. Functions()
# measreinit #####################
##################################


def adb_data_signal_measurements_reinit_main():
    """to clear measurement data for new measurement
    """
    global lst_l1, lst_l2, tv1_lst1, tv1_lst2, tv1_lst3, tv2_lst1, tv2_lst2, tv2_lst3,\
        SignalStrength, SS, sss, ip, mip, mmtu, wip, mif, wif, RMq, procdata, devdata

    logger.debug('---------------: call adb_data_signal_measurements_reinit_main')
    SignalStrength = []
    SS = []  # SignalStrength per RadioModule
    sss = []  # SS splitted to values for Androids ver <10
    tv1_lst1 = []
    tv1_lst2 = []
    tv1_lst3 = []
    tv2_lst1 = []
    tv2_lst2 = []
    tv2_lst3 = []

    for i in [0, 1, 3]:
        procdata[i] = [] # clear measurements data only
    # lst_l1 = ['']
    # lst_l2 = ['']


def adb_data_reinit_main():
    """to clear all data for new connection//data investigation
    """    
    global lst_l1, lst_l2, tv1_lst1, tv1_lst2, tv1_lst3, tv2_lst1, tv2_lst2, tv2_lst3,\
        SignalStrength, SS, sss, ip, mip, mmtu, wip, mif, wif, RMq, procdata, devdata # , p6

    logger.debug('---------------: call ADB_data_reinit_main()')
    # UNKNOWN_VALUE = '2147483647'
    # torun = 'c:\\adb\\adb.exe  '
    # PARAM_1 = 'shell  dumpsys telephony.registry |grep '
    # PARAM_1a = 'shell  "dumpsys telephony.registry |grep '
    # PARAM_2 = ['mServiceState',
    #            'mSignalStrength',
    #            'mCellInfo',
    #            'mPreciseDataConnectionState',
    #            'mPhoneCapability',
    #            'mBarringInfo']
    SignalStrength = []
    SS = []  # SignalStrength per RadioModule
    sss = []  # SS splitted to values for Androids ver <10
    ip = []  # IP addresses with UP interfaces
    mip = ''  # mobile IP addresses with UP interfaces
    mmtu = ''  # MTU of the UP mobile itf
    wip = ''  # WiFi IP addresses with UP interfaces
    mif = ''  # rmnet UP interface name
    wif = ''  # WiFi  UP interface name
    RMq = 0  # initial quantity of Radio Modules
    p6 = []
    iphonesubinfo_registers = []  # array of answers to registers 0..29
    imei = [None, None]  # for IMEI
    imsi = [None, None]  # for IMSI
    isdn = [None, None]  # for MSISDNs
    procdata = [[], ] * 15  # returned ADB strings
    lst_l1 = ['']
    lst_l2 = ['']
    tv1_lst1 = []
    tv1_lst2 = []
    tv1_lst3 = []
    tv2_lst1 = []
    tv2_lst2 = []
    tv2_lst3 = []

# 01
############################################################################################
# Main. Functions()
# 01 #############################

def get_data_from_adb_device_connect_main_01():
    """ 
    This procedure connecting DUT via ADB and check that developer mode and ADB connection are enabled at DUT,
    inflating getprop parameters to global vars:
    Output (global):
    datastr  - initial data ={None} (dict)
    RMq - quantity of Radio Modules 
    DevModel (str)
    Androidver (str) from getprop ro.build.version.release
    intAndroidver (int) = int(Androidver)
    Nettype (str) from getprop gsm.network.type
    NetPLMNs ([str]) from getprop gsm.operator.numeric
    DevMan (str) from getprop ro.product.manufacturer   
    DevDev (str) from getprop ro.product.device         
    DevMod (str) from getprop ro.product.model          
    DevName (str) from getprop ro.product.name           
    DevName1 (str) from getprop persist.sys.device_name
    NetOps (str) from getprop gsm.operator.alpha
    # Get Device Vendor, Name, Model etc
    # ====================================
    # ro.product.manufacturer   DevMan
    # ro.product.device         DevDev
    # ro.product.model          DevMod
    # ro.product.name           DevName
    # persist.sys.device_name   DevName1
    # gsm.operator.alpha        NetOps
    """
    logger.debug('---------------: call ADB_device_connect_main01')
    global k, RMq, procdata, devdata, NetPLMNs, NetOps, intAndroidver, Androidver, DevModel, DevMan, DevDev, DevMod,\
        DevName, DevName1, Nettype, datastr, SDK_ver, abi_list, PKG_DIR, sim_state, Device_SN

    p = (subprocess.run(torun + 'devices -l', capture_output=True, text=True, shell=True))
    pp = (re.split("\r|\n", p.stdout))
    DevModel = get_value_from_string(pp[1], 'model:', ' ')
    logger.info('Device: ' + str(DevModel))

    RMq = get_radio_modules_qty()
    Androidver = get_android_version()
    intAndroidver = int(float(Androidver[:2]))
    Nettype = get_net_types()
    NetPLMNs = get_PLMNs()
    DevDev = get_product_device()
    DevMod = get_product_model()
    DevMan = get_device_manufacturer()
    DevName = get_product_name()
    DevName1 = get_persist_dev_name()
    SDK_ver =  get_version_SDK()
    sim_state = get_sim_state()
    Device_SN = get_Device_SN()
    NetOps = get_NetOps()

    abi_list = get_abilist()
    if abi_list == 'armeabi-v7a,armeabi' :
        PKG_DIR = 'c:\\adb\\install\\iperf\\armeabi-v7a'
    elif 'arm64-v8a' in abi_list:
        PKG_DIR = 'c:\\adb\\install\\iperf\\arm64-v8a'
    elif 'x86_64' in abi_list:
        PKG_DIR = 'c:\\adb\\install\\iperf\\x86_64'
    elif 'x86' in abi_list:
        PKG_DIR = 'c:\\adb\\install\\iperf\\x86'
    else:
        logging.error(f'Supported ABI not found, ABI: {abi_list}')

def get_radio_modules_qty():
    ''' Get quantity of Phone Ids == quantity of Radio modules
        using   "dumpsys telephony.registry | grep 'Phone Id='"
        Return: RMq, devdata (global)
    '''
    global devdata
    a = torun + 'shell "dumpsys telephony.registry |grep ' + "'" + 'Phone Id=' + "'"+'"'
    p = (subprocess.run(a, capture_output=True, text=True, shell=True))
    pp = (re.split("\r|\n", p.stdout))
    RMq = 0
    for a in pp:
        if 'Phone Id=' in a:
            RMq += 1
    if RMq > 0:
        for j in range(RMq):
            devdata.append(
                dict(datastr))  # for each RadioModule = sim slot explicitly copy a dictionary to array per sim slots
            logger.debug(str(pp[j]))
    logger.info('RadioModules = ' + str(RMq))
    return RMq

def get_android_version():
    # Get Android version to str var Androidver and int var intAndroidver
    s = torun + 'shell getprop ro.build.version.release'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    if 'error: device unauthorized' in p.stderr:
        logger.debug(p.stderr)
        logger.error(
            'Please, authorize ADB debugging on the device (check ADB debugging allowed from this host) ')
        app = QtWidgets.QApplication(sys.argv)
        window = QtWidgets.QWidget()
        window.setWindowTitle("ADB phone data extractor")
        window.resize(400, 60)
        label = QtWidgets.QLabel(
            "<center> Please, authorize ADB debugging on the device (check ADB debugging allowed from this host) "
            "</center>")
        btnQuit = QtWidgets.QPushButton("&Close window")
        vbox = QtWidgets.QVBoxLayout()
        vbox.addWidget(label)
        vbox.addWidget(btnQuit)
        window.setLayout(vbox)
        btnQuit.clicked.connect(app.quit)
        window.show()
        sys.exit(app.exec_())
        # exit(1)
    else:
        a = p.stdout
        Androidver = a.replace('\n', '')  # clean from '\n'
        logger.info('Android version:' + Androidver)
        return Androidver

def get_wif_main():
    '''Get wifi interface name from getprop wifi.interface'''
    s = torun + 'shell getprop wifi.interface'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    a = a.replace('\n', '')  # .replace(':', '')
    return a

def get_net_types():
    # Get Network type Nettype[j]
    s = torun + 'shell getprop gsm.network.type'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    a = a.replace('\n', '')  # clean from '\n'
    pp = re.split(',', a)
    Nettype = pp
    logger.info('Connected mobile network types:' + str(Nettype))
    return Nettype

def get_PLMNs():
    # Get PLMNs
    s = torun + 'shell getprop gsm.operator.numeric'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    a = a.replace('\n', '')
    pp = re.split(',', a)
    NetPLMNs = pp
    if len(Nettype) > 1:
        NetPLMNs.append('')
    logger.info('Connected mobile PLMNs:' + str(NetPLMNs))
    return NetPLMNs

def get_product_device():
    s = torun + 'shell getprop ro.product.device'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    DevDev = a.replace('\n', '')  # clean from '\n'
    logger.info('Device:' + str(DevDev))
    return DevDev

def get_device_manufacturer():
    s = torun + 'shell getprop ro.product.manufacturer'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    DevMan = a.replace('\n', '')  # clean from '\n'
    logger.info('Device Manufacturer:' + str(DevMan))
    return DevMan

def get_product_model():
    s = torun + 'shell getprop ro.product.model'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    DevMod = a.replace('\n', '')  # clean from '\n'
    logger.info('Device Model:' + str(DevMod))
    return DevMod

def get_persist_dev_name():
    s = torun + 'shell getprop persist.sys.device_name'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    DevName1 = a.replace('\n', '')  # clean from '\n'
    logger.info('Device Name1:' + str(DevName1))
    return DevName1

def get_sim_state():
    s = torun + 'shell getprop gsm.sim.state'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    sim_state = a.replace('\n', '').split(',')
    logger.info(f'SIM card(s) state: {sim_state}')
    if RMq != len(sim_state):
        logger.error(f'Radio Modules: {RMq}, <> SIM card(s) state: {sim_state}')
    return sim_state

def get_product_name():
    s = torun + 'shell getprop ro.product.name'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    DevName = a.replace('\n', '')  # clean from '\n'
    logger.info('Device Name:' + str(DevName))
    return DevName

def get_NetOps():
    ''' Get Operators of RadioModules
    '''
    s = torun + 'shell getprop gsm.operator.alpha'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    a = a.replace('\n', '')  # clean from '\n'
    pp = re.split(',', a)
    if len(pp) < 2:
        NetOps = ['N/A']
        if RMq > 1:
            NetOps.append('N/A')
    else:
        NetOps = pp
    logger.info('Connected mobile network:' + str(NetOps))
    return NetOps

def get_version_SDK():
    ''' get SDK version from getprop ro.build.version.sdk
    :return: SDK_ver
    '''
    s = torun + 'shell getprop ro.build.version.sdk'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    SDK_ver = a.replace('\n', '')  # clean from '\n'
    logger.info(f'SDK_ver: {SDK_ver}')
    return SDK_ver

def get_abilist():
    ''' run adb shell getprop ro.product.cpu.abilist for knowledge wich type of iperf clients packages should be loaded
    :return: abilist
    '''
    s = torun + 'shell getprop ro.product.cpu.abilist'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout.replace('\n','')
    logger.info(f'ABI: {a}')
    if len(a) > 6:
        return a
    else:
        return None

def request_adb_service_call(cmd):
    p = (subprocess.run(cmd, capture_output=True, text=True, shell=True, encoding='utf8'))
    ans = p.stdout
    return ans

def get_iphonesubinfo_main():
    ''' Inflating iphonesubinfo for IMEI, IMSI, MSISDN if possible.
    here are the TRANSACTION CODES for the iphonesubinfo service in android-5.0.0_r1:
     1  getDeviceId					                15  getMsisdn
     2  getDeviceIdForSubscriber                    16  getMsisdnForSubscriber
     3  getImeiForSubscriber                        17  getVoiceMailNumber
     4  getDeviceSvn                                18  getVoiceMailNumberForSubscriber
     5  getSubscriberId                             19  getCompleteVoiceMailNumber
     6  getSubscriberIdForSubscriber                20  getCompleteVoiceMailNumberForSubscriber
     7  getGroupIdLevel1                            21  getVoiceMailAlphaTag
     8  getGroupIdLevel1ForSubscriber               22  getVoiceMailAlphaTagForSubscriber
     9  getIccSerialNumber                          23  getIsimImpi
    10  getIccSerialNumberForSubscriber             24  getIsimDomain
    11  getLine1Number                              25  getIsimImpu
    12  getLine1NumberForSubscriber                 26  getIsimIst
    13  getLine1AlphaTag                            27  getIsimPcscf
    14  getLine1AlphaTagForSubscriber               28  getIsimChallengeResponse
                                                    29  getIccSimChallengeResponse
    '''
    global Device_SN, sim_state, imei, imsi, isdn, iphonesubinfo_registers
    toshell = torun + ' shell '
    for i in range(30):
        parm = ('"service call iphonesubinfo'
            + f' {i} | grep -o '
            + "'[0-9a-f]\{8\} ' | tail -n+3 | while read a; do echo -n"
            + ' \\\\u${a:4:4}\\\\u${a:0:4}; done"')
        cmd = f' {toshell}  {parm}'
        # print (cmd)
        ans = request_adb_service_call(cmd)
        # iphonesubinfo_registers.append(f'{i}:\t{ans}')
        n = 0 # no sim loaded
        if len(sim_state) >1:
            if sim_state[0] == 'LOADED': # sim #0 loaded
                n = 0
            elif sim_state[1] == 'LOADED': # no sim #0, loaded sim #1
                n = 1
        iphonesubinfo_registers.append(ans)
    for i in range(len(iphonesubinfo_registers)):
        res1 = re.search(r'\d{8,}', iphonesubinfo_registers[i])
        if res1:
            if i in [1,2]: # can be IMEI
                imei[0] = iphonesubinfo_registers[i]
            elif i in [4,5]: # can be IMEI of  2nd RM
                if iphonesubinfo_registers[i] != imei[0]:
                    imei[1] = iphonesubinfo_registers[i]
            elif i in [7, 8, 9]: # can be IMSI
                if imsi[n]:
                    if imsi[n] != iphonesubinfo_registers[i]:
                        if sim_state[1-n] == 'LOADED':
                            imsi[1-n] = iphonesubinfo_registers[i]
                else:
                        if sim_state[n] =='Loaded':
                            imsi[n] = iphonesubinfo_registers[i]
                        else:
                            pass  # reported imsi not for loaded sim, from phone stored data etc.
                        # if (sim_state[0] != 'LOADED' and sim_state[1] == 'LOADED'):
                        #     imsi[1-n] = iphonesubinfo_registers[i]
                        # else:
                        #     pass  # if no sim loaded, no imsi
            elif i in [15, 16]: # MSISDN
                if not isdn[n]:
                    isdn[n] = iphonesubinfo_registers[i].replace('\x00','').replace('\x00','')
                else:
                    if isdn[n] != iphonesubinfo_registers[i].replace('\x00','').replace('\x00',''):
                        isdn[1-n] = iphonesubinfo_registers[i].replace('\x00','').replace('\x00','')
            elif i == 27:
                nbr = get_value_from_string(iphonesubinfo_registers[i],'sip:','@')
                if nbr:
                    if not imsi[0]:
                        imsi[0] = nbr
                    else:
                        if (not imsi[1] and nbr not in imsi[0]):
                            imsi[1] = nbr
            logging.debug(f'iphonesubinfo service # {i} \t {iphonesubinfo_registers[i]}')
    logging.debug('==================done======================')
    if not imei[0]:
        imei[0] = get_imei1()
    if imei[0] and not imei[1]:
        imei[1] = get_imei2()
        # (imsi[1],imsi[0]) = (imsi[0],imsi[1])
        # (imei[1],imei[0]) = (imei[0],imei[1])
    logging.debug(f'imei1 = {imei[0]}, imei2 = {imei[1]}')
    logging.debug(f'imsi1 = {imsi[0]}, imsi2 = {imsi[1]}')
    logging.debug(f'msisdn1 = {isdn[0]}, msisdn2 = {isdn[1]}')

def get_Device_SN():
    ''' Get Device S/N from getprop ro.serialno
    :return: Device_SN
    '''
    s = torun + 'shell getprop ro.serialno'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    sn = p.stdout.replace('\n','')
    logger.info(f'S/N: {sn}')
    if len(sn) > 4:
        return sn
    else:
        return None


def get_imei1():
    s = torun + 'shell getprop persist.radio.imei2'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    logger.info(f'IMEI_1: {a}')
    if len(a) > 10:
        return a
    else:
        return None

def get_imei2():
    s = torun + 'shell getprop persist.radio.imei2'
    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
    a = p.stdout
    logger.info(f'IMEI_2: {a}')
    if len(a) > 10:
        return a
    else:
        return None


############################################################################################
# Main. Functions()
# Meas ###########################
##################################

def get_signal_measurement_data_from_adb():
    """ This procedure inflating radio modules states and signal level to global vars from connected DUT via ADB:
    Input: None
    Output (global):
    [0][1] procdata[0]     - 'mServiceState'
    [0][1] procdata[1]     - 'mSignalStrength'
    [X] procdata[2]     - None 'mCellInfo'
    [0] procdata[3]     - 'mPreciseDataConnectionState'
    [X] procdata[4]     - None 'mPhoneCapability'
    [X] procdata[5]     - None 'mBarringInfo'
    SS              - SignalStrength
    SignalStrength  - SignalStrength
    datastr         - initial data ={None} (dict)
    """
    logger.debug('---------------: call ADB_device_connect_meas')
    global procdata, SS, SignalStrength, datastr

    # procdatta[0..5] =
    #   (0)ServiceState), (1)SignalStrength), (2)CellInfo', (3)PreciseDataConnectionState,
    #       (4)PhoneCapability', (5)BarringInfo'
    # PARAM_1a = 'shell  "dumpsys telephony.registry |grep '  # for ADB data inflating with ""
    # PARAM_2 = ['mServiceState',               0   OK
    #            'mSignalStrength',             1   OK
    #            'mCellInfo',                   2   not used
    #            'mPreciseDataConnectionState', 3   OK
    #            'mPhoneCapability',            4   not used 
    #            'mBarringInfo']                5   not used

    for i in [0, 1, 3]:
        '''
        PARAM_1a = 'shell "dumpsys telephony.registry |grep '  # for ADB data inflating with "
        PARAM_2 = ['mServiceState',  # for ADB data inflating (from telephony.registry service)
                   'mSignalStrength',
                   'mCellInfo',
                   'mPreciseDataConnectionState',
                   'mPhoneCapability',
                   'mBarringInfo']
        i = 0 # mServiceState
        i = 1 # mSignalStrength
        i = 3 # mPreciseDataConnectionState
        '''
        logger.debug(str(i) + ' ' + str(PARAM_2[i]) + ':')
        s = torun + PARAM_1a + '"' + PARAM_2[i] + '"'
        p = (subprocess.run(s, capture_output=True, text=True, shell=True))
        pp = (re.split(PARAM_2[i] + '=', p.stdout))

        # if len(pp) > 1 and len(pp[0]) < 5:
        if  1 < len(pp[0]) < 5:
            del (pp[0])
        procdata[i] = pp
        logger.debug(str(i) + ' ' + str(procdata[i]))

def get_ip_data_from_adb_device_main():
    """ This procedure inflating radio modules states and radio level to global vars  from connected DUT via ADB::
    Output (global):
    k           - procdata index
    procdata[6] - ip -c a
    dclnk       - 'mDataConnectionLinkProperties'
    mif - mobile interface
    mip - mobile IP
    mmtu - mobile MTU
    wif - WiFi interface
    wip - WiFi IP
    etc
    """
    logger.debug('---------------: call ADB_device_connect_main02')
    global k, RMq, procdata, mif, mmtu, mip, wif, wip, datastr, dclnk  # , p6
    #################
    # 6) interfaces
    #################
    dclnk = []
    if intAndroidver < 10:  # and/or procdata[3]==0
        s = torun + 'shell dumpsys telephony.registry|grep mDataConnectionLinkProperties'
        p = (subprocess.run(s, capture_output=True, text=True, shell=True))
        dclnk = p.stdout
        if len(dclnk) > 2:
            logger.debug(dclnk[:200])
            logger.info('IP =' + str(get_value_from_string(dclnk, 'InterfaceName: ', ' ')))
            logger.info('If =' + str(get_value_from_string(dclnk, 'LinkAddresses: ', ' ')))
            logger.info('Routes =' + str(get_value_from_string(dclnk, 'Routes: ', ']')))
            logger.info('DNS =' + str(get_value_from_string(dclnk, 'DnsAddresses: ', ']')))

    #    IP = rmnet_data0
    #    If = [100.123.91.44/29,]
    #    Routes = [0.0.0.0/0 -> 100.123.91.45 rmnet_data0,
    #    DNS = [10.153.3.204,10.153.3.212,
    k = 6
    logger.debug('#' + str(k) + ')\n')
    param3 = ' shell ip a'
    p = (subprocess.run(torun + param3, capture_output=True, text=True, shell=True))
    procdata[6]=re.split("\r|\n", p.stdout)
    logger.debug(p.stdout)
    p6 = []
    for i in range(len(procdata[6])):
        if len(procdata[6][i]) != 0:
            p6.append(procdata[6][i])

    logger.debug('============= в цикле: =========')
    procdata[6] = p6
    for i in range(len(procdata[6])):
        logger.debug(str(i) + '   ' + str(procdata[6][i]))

    # Finding interfaces in UP state and IP addresses
    for j in range(len(procdata[6])):
        if ('UP,LOWER_UP' in procdata[6][j] or
                'scope global' in procdata[6][j]):
            logger.debug(str(j) + procdata[6][j])
            if 'inet ' in procdata[6][j]:
                ip.append(get_value_from_string(procdata[6][j], 'inet ', ' '))
                if 'rmnet' in procdata[6][j - 2]:
                    mip = get_value_from_string(procdata[6][j], 'inet ', ' ')
                    mif = get_value_from_string(procdata[6][j - 2], '', '<')[3:]
                    mmtu = get_value_from_string(procdata[6][j - 2], ' mtu ', ' ')
                    logger.info('mIP=' + mip)
                    logger.info('mIF=' + mif)
                    logger.info('MTU=' + mmtu)
                elif 'wlan' in procdata[6][j - 2]:
                    wip = get_value_from_string(procdata[6][j], 'inet ', ' ')
                    wif = get_value_from_string(procdata[6][j - 2], '', '<')[4:]
    if not wif:
        wif = get_wif_main()
    logger.info('wIP=' + wip)
    logger.info('wIF=' + wif)

##################################
# WiFiScanner ####################
##################################


def get_wifi_scanner_data_main():
    """
    This procedure connecting DUT via ADB and inflating radio modules states and level to global vars:
    Output: 
        global:
    WiFiScanData - WiFi scanning data from the device
    """
    logger.debug('---------------: call ADB_device_WiFiScanner_main')
    global WiFiScanData
    #    adb shell dumpsys wifiscanner => слишком много мусора!
    # c:\adb\adb.exe  shell "dumpsys wifiscanner |awk '/Latest scan results:/,/Latest native pno/'"
    if DevModel:
        param2 = '/Latest scan results:/,/Latest native pno/'
        s = torun + PARAM_1b + "'" + param2 + "'" + '"'
        print(s)
        p = (subprocess.run(s, capture_output=True, text=True, shell=True))
        WiFiScanData = p.stdout[:-32]


############################################################################################
# Main. Functions()
# 03 #############################


def get_wifi_data_from_adb_device_main():
    """
    This procedure inflating radio modules states and signal level to global vars  from connected DUT via ADB::
    Output (global):
    procdata[7][0] - 'shell dumpsys wifi | grep mWifiInfo"'   (wifi signal, speed etc.)
    procdata[7][1] - 'shell dumpsys wifi' (wifi status)
    """
    logger.debug('---------------: call get_wifi_data_from_adb_device_main')
    global k, procdata
    #################
    # 7) WiFi
    #################
    k = 7
    # [7][0] = WiFi levels
    logger.debug('#' + str(k) + 'WiFi | grep mWifiInfo )')
    p = (subprocess.run(torun + PARAM_1c, capture_output=True, text=True, shell=True))
    procdata[k].append(p.stdout[:1000]) # --> procdata[7][0]
    if p.returncode == 0:
        if len(p.stdout) > 2:
            logger.debug(procdata[k][:200])
    else:
        logger.debug(f'# ERROR: {p.stderr}')

    # [7][1] = WiFi state
    parm = ' shell dumpsys wifi'
    p = (subprocess.run(torun + parm, capture_output=True, text=True, shell=True))
    procdata[k].append(p.stdout[:1000])  # ----> [procdata[7][1]
    if p.returncode == 0:
        if len(p.stdout) > 2:
            logger.debug(procdata[k][:200])
    else:
        logger.debug(f'# ERROR: {p.stderr}')


def get_disk_data_from_adb_device_main():
    """
    This procedure inflating flash memory size to global var  from connected DUT via ADB::
    Output (global):
    procdata[8]    - 'shell df -H' (disk status)
    """
    logger.debug('---------------: call get_disk_data_from_adb_device_main')
    global k, procdata
    #################
    #  8) Disk info
    #################
    k = 8
    logger.debug('#' + str(k) + ')')
    parm = ' shell df -H'  #  /storage/emulated
    p = (subprocess.run(torun + parm, capture_output=True, text=True, shell=True))
    procdata[k] = re.split("\r|\n", p.stdout)
    if len(p.stdout) > 2:
        logger.debug(p.stdout[:1500])
        for j in range(min(len(procdata[k]), 60)):
            logger.debug(str(procdata[k][j]))


def get_battery_data_from_adb_device_main():
    """
    This procedure inflating flash memory size to global var  from connected DUT via ADB::
    Output (global):
    procdata[8]    - 'shell df -H' (disk status)
    """
    logger.debug('---------------: call get_battery_data_from_adb_device_main')
    global k, procdata
    #################
    # 9) Battery info
    #################
    k = 9
    logger.debug('#' + str(k) + ')')
    param = ' shell dumpsys battery'  # |grep '
    p = (subprocess.run(torun + param, capture_output=True, text=True, shell=True))
    procdata[9] = re.split("\r|\n", p.stdout)
    if len(p.stdout) > 2:
        logger.debug(p.stdout[:1500])
        for j in range(min(len(procdata[k]), 20)):
            logger.debug(str(procdata[k][j]))


def get_RAM_data_from_adb_device_main():
    """
    This procedure inflating RAM size to global var  from connected DUT via ADB::
    Output (global):
    procdata[10] - 'shell free -h' (memory status#1)
    procdata[11] - 'shell cat /proc/meminfo' (memory status#2)
    procdata[12] - 'shell vmstat' (memory status#3)
    procdata[13] - 'shell top -n1' (memory status#4)
    """
    logger.debug('---------------: call get_RAM_data_from_adb_device_main')
    global k, procdata
    #################
    #  10..13) RAM
    #################
    # shell free -h
    # shell cat /proc/meminfo
    # shell vmstat
    # shell top -n1
    k = 10
    logger.debug('#' + str(k) + ')')
    param4 = ' shell free -h'
    p = (subprocess.run(torun + param4, capture_output=True, text=True, shell=True))
    procdata[k] = re.split("\r|\n", p.stdout)
    k = 11
    logger.debug('#' + str(k) + ')')
    param4 = ' shell cat /proc/meminfo'
    p = (subprocess.run(torun + param4, capture_output=True, text=True, shell=True))
    procdata[k] = re.split("\r|\n", p.stdout)
    k = 12
    logger.debug('#' + str(k) + ')')
    param4 = ' shell vmstat'
    p = (subprocess.run(torun + param4, capture_output=True, text=True, shell=True))
    procdata[k] = re.split("\r|\n", p.stdout)
    k = 13
    logger.debug('#' + str(k) + ')')
    param4 = ' shell top -n1'
    p = (subprocess.run(torun + param4, capture_output=True, text=True, shell=True))
    procdata[k] = re.split("\r|\n", p.stdout)


def get_data_from_adb_device_main_03():
    """
    This procedure inflating data to global vars  from connected DUT via ADB::
    """
    logger.debug('---------------: call ADB_device_connect_main03')
    get_wifi_data_from_adb_device_main() # ---> procdata[7]
    get_disk_data_from_adb_device_main() # ---> procdata[8]
    get_battery_data_from_adb_device_main() # ---> procdata[9]
    get_RAM_data_from_adb_device_main() # ---> procdata[10..13]

############################################################################################
# Main. Functions()
# 04 #############################

def get_data_from_adb_device_connect_main_04():
    """ This procedure inflating radio modules states and signal LEVELS to global vars from connected DUT via ADB:
    Input: none
    Output (global):
    k - procdata index
    procdata[3] - patch for Androidver <10 for 'mPreciseDataConnectionStates'
    ServStates[i]  - split procdata[0][i] per i = RadioModule
    """
    logger.debug('---------------: call get_data_from_adb_device_connect_main04')
    global k, RMq, procdata, ServStates
    #################
    # Data processing
    #################
    # public String toString() {
    #    return ("SignalStrength:"
    # 1           + " " + mGsmSignalStrength   mSS
    # 2           + " " + mGsmBitErrorRate	    BER
    #
    # 3           + " " + mCdmaDbm		    RSSI
    # 4           + " " + mCdmaEcio            ECIO
    #
    # 5           + " " + mEvdoDbm		    RSSI
    # 6           + " " + mEvdoEcio	    ECIO
    # 7           + " " + mEvdoSnr		    SINR
    #
    # 8           + " " + mLteSignalStrength   SS
    # 9           + " " + mLteRsrp		    RSRP
    # 10           + " " + mLteRsrq	    RSRQ
    # 11           + " " + mLteRssnr	    SINR*10
    # 12           + " " + mLteCqi             CQI
    #######################################################################
    #    datastr = {'mRegCS':None,'mRegPS': None,'mCNOp':None,
    #                'mCSRT':None, 'mPSRT':None, 'mPLMN':None, 'mRATC':None,
    #                'mConn':None,'mAPN':None,
    #               'mChan': None,'mBW': None, 'RTech':None,
    #               'mSS':None, 'BER':None,
    #               'EcNo':None,'RSCP':None,'SNR':None, 'ECIO':None,
    #               'RSSI':None, 'RSCP':None, 'RSRP':None, 'RSRQ':None, 'SINR':None, 'CQI':None,
    #               'ssRsrp':None, 'ssRsrq':None, 'ssSinr':None,
    #               'mIF':None, 'mIP':None,'mMTU':None,
    #                 'WiFiConn': None, 'wIF': None, 'wIP': None,
    #                 'WiFi_SSID': None, 'WiFi_Generation': None, 'wRSSI': None,
    #                 'WiFi_link_speed': None, 'WiFi_TX_link_speed': None, 'WiFi_RX_link_speed': None}

    if len(procdata[3]) == 1:  # mPreciseDataConnectionStates
        procdata[3] = re.split("\r|\n", procdata[3][0])  # при RMq = 2 разбивка на RM0, RM1..
        if procdata[3][-1] == '':
            del (procdata[3][-1])
            logger.debug('procdata[3][-1] removed')
        for i in range(len(procdata[3])):
            logger.debug(str(i) + ':' + str(procdata[3][i]))
    logger.debug('RMq=' + str(RMq) + ', len=' + str(len(procdata[3])))
    #  костыль на случай Android <10  и только 1 записи mPreciseDataConnectionStates, которую надо реплицировать
    #  по кол-ву радиомодулей
    if (RMq > len(procdata[3]) and len(procdata[3]) == 1):
        pptmp = []
        logger.debug('RMq=' + str(RMq) + '\nAndroid<10 and len(procdata[3])==1')
        for j in range(RMq):
            pptmp.append(procdata[3][0])
        procdata[3] = pptmp

    if intAndroidver < 10:
        logger.debug('Android<10')
        ServStates = []
        for i in range(RMq):
            ServStates.append(re.split(" ", procdata[0][i]))
        logger.debug('Android <10, ServStates=:')
        for i in range(RMq):
            for j in range(len(ServStates[i])):
                logger.debug(str(i) + ' ' + str(j) + ' ' + str(ServStates[i][j]))


############################################################################################
# Main. Functions()
# 05 ==dataproc ##################



def proceed_adb_device_data():
    """
    This procedure is for data processing prom previously inflated data to global vars:
    Input: none
    Output: global vars:
    datastr         - initial data ={None} (dict)
    devdata         - output data (dict)
    sss             - SignalStrength data split for Android ver <10
    SS              - SignalStrength var.
    SignalStrength  - SignalStrength
    """
    logger.debug('---------------: call ADB_device_dataproc')
    global devdata, SS, sss, SignalStrength, datastr, idxnr

    logger.debug('RMq=' + str(RMq))
    for j in range(RMq):  # for each Radio Module:
        #   split SignalStrength by 'CellSignalStrength' and 'primary' (Android 10+)
        if intAndroidver >= 10:
            SignalStrength = re.split("CellSignalStrength|primary=", procdata[1][j])
            SS.append(SignalStrength)
            logger.debug('\n\n Splitted by CellSignalStrength|primary:')
        else:  # if Androidver <10
            SignalStrength = ''
            SS = ''
            logger.debug('sss:')
            sss.append(re.split(" ", procdata[1][j]))  # SignalStrength data split for Android ver <10
            for i in range(len(sss[j])):
                logger.debug(str(i) + ' ' + str(sss[j][i]))
        if intAndroidver >= 10:
            logger.debug('len(SignalStrength)=' + str(len(SignalStrength)))
            # find idx of active RT
            logger.debug('Searching for RT idx')
            for i in range(len(SS[j]) - 1):  # do not use SS[j][-1]
                logger.debug(str(i) + ' ' + str(j) + ' ' + str(SS[j][i]))
                if SS[j][-1][:3] in SS[j][i][:3]:  # if RTec=LTE/Wcd/Gsm/.... in SignalStrength[j]
                    idx = i
                    logger.debug('idx = ' + str(idx))
                    break
            else:
                idx = 1
            # find idx of NR
            logger.debug('Searching for NR idx')
            for i in range(len(SS[j]) - 1):  # do not use SS[j][-1]
                if 'Nr:' in SS[j][i][:3]:  # if RTec=LTE/Wcd/Gsm/.... in SignalStrength[j]
                    idxnr = i # default idxnr = -1, changed there if NR records found
                    logger.debug('idxNR = ' + str(idxnr))
                    break
            else:
                idx = 1

        if len(SignalStrength) > 0:
            logger.debug(SignalStrength[-1][:10])
            logger.info('Technology Index idx=' + str(idx))
            logger.info('RadioModule ' + str(j) + ':')
            for i in range(len(SignalStrength)):
                logger.debug(str(i) + ': ' + SignalStrength[i])
        if get_value_from_string(procdata[0][j], 'mVoiceRegState=', ','):
            devdata[j]['mRegCS'] = get_value_from_string(procdata[0][j], 'mVoiceRegState=', ',')[
                                   1:]  # remove digit value before '('
        if get_value_from_string(procdata[0][j], 'mDataRegState=', ','):
            devdata[j]['mRegPS'] = get_value_from_string(procdata[0][j], 'mDataRegState=', ',')[1:] # rem dig before '('
        devdata[j]['mChan'] = get_value_from_string(procdata[0][j], 'mChannelNumber=', ',')
        devdata[j]['mBW'] = get_value_from_string(procdata[0][j], 'mCellBandwidths=[', ',')
        if (get_value_from_string(procdata[0][j], 'OperatorAlphaLong=', ',') and
                get_value_from_string(procdata[0][j], 'OperatorAlphaLong=', ',') != '<MASKED>'):
            devdata[j]['mCNOp'] = get_value_from_string(procdata[0][j], 'OperatorAlphaLong=', ',')
        else:
            if len(NetOps) >= j:
                devdata[j]['mCNOp'] = NetOps[j]
        devdata[j]['mCSRT'] = get_value_from_string(procdata[0][j], 'RilVoiceRadioTechnology=', ',')
        devdata[j]['mPSRT'] = get_value_from_string(procdata[0][j], 'RilDataRadioTechnology=', ',')
        if (get_value_from_string(procdata[0][j], 'mMnc=', ' ') and
                get_value_from_string(procdata[0][j], 'mMcc=', ' ')):
            devdata[j]['mPLMN'] = (get_value_from_string(procdata[0][j], 'mMcc=', ' ')
                                   + get_value_from_string(procdata[0][j], 'mMnc=', ' '))
        else:
            devdata[j]['mPLMN'] = NetPLMNs[j]
        devdata[j]['mRATC'] = get_value_from_string(procdata[0][j], 'accessNetworkTechnology=', ' ')
        if (len(procdata[3]) > j and
           not Measonly):
            if len(procdata[3]) > 0:  # Androids <9 has no PreciseDataConnectionState record => procdata[3]
                devdata[j]['mAPN'] = get_value_from_string(procdata[3][j], 'APN:', ',')
                devdata[j]['mIF'] = mif
                devdata[j]['mIP'] = mip
                devdata[j]['mMTU'] = mmtu
                devdata[j]['mConn'] = get_value_from_string(procdata[3][j], 'Data Connection state:', ',')
            else:
                devdata[j]['mAPN'] = 'N/A'
                devdata[j]['mIF'] = mif
                devdata[j]['mIP'] = mip
                devdata[j]['mMTU'] = mmtu
                devdata[j]['mConn'] = 'N/A'
        devdata[j]['mChan'] = get_value_from_string(procdata[0][j], 'mChannelNumber=', ',')
        devdata[j]['mBW'] = get_value_from_string(procdata[0][j], 'mCellBandwidths=[', ']')
#  for Androidver >=9
        if (intAndroidver >= 10 and len(SS[j]) > idx):
            if SignalStrength[-1][:3] == 'Wcd':
                devdata[j]['RTech'] = 'WCDMA'
            else:
                devdata[j]['RTech'] = SignalStrength[-1][:3]
            logger.debug('RM = ' + str(j) + 'idx = ' + str(idx))
            if get_value_from_string(SS[j][idx], 'ss=', ' '):
                devdata[j]['mSS'] = get_value_from_string(SS[j][idx], 'ss=', ' ')
            else:
                devdata[j]['mSS'] = 'N/A'
            if get_value_from_string(SS[j][idx], 'rscp=', ' '):
                devdata[j]['RSCP'] = get_value_from_string(SS[j][idx], 'rscp=', ' ')
            else:
                devdata[j]['RSCP'] = 'N/A'
            if get_value_from_string(SS[j][idx], 'ber=', ' '):
                devdata[j]['BER'] = int(get_value_from_string(SS[j][idx], 'ber=', ' '))
            else:
                devdata[j]['BER'] = 'N/A'
            if get_value_from_string(SS[j][idx], 'rssi=', ' '):
                devdata[j]['RSSI'] = get_value_from_string(SS[j][idx], 'rssi=', ' ')
            else:
                devdata[j]['RSSI'] = 'N/A'
            if get_value_from_string(SS[j][idx], 'rsrp=', ' '):
                devdata[j]['RSRP'] = get_value_from_string(SS[j][idx], 'rsrp=', ' ')
            else:
                devdata[j]['RSRP'] = 'N/A'
            if get_value_from_string(SS[j][idx], 'rsrq=', ' '):
                devdata[j]['RSRQ'] = get_value_from_string(SS[j][idx], 'rsrq=', ' ')
            else:
                devdata[j]['RSRQ'] = 'N/A'
            if get_value_from_string(SS[j][idx], 'rssnr=', ' '):
                devdata[j]['SINR'] = int(get_value_from_string(SS[j][idx], 'rssnr=', ' ')) / 10
            else:
                devdata[j]['SINR'] = 'N/A'
            if get_value_from_string(SS[j][idx], 'ecno=', ' '):
                devdata[j]['EcNo'] = (get_value_from_string(SS[j][idx], 'ecno=', ' '))
            else:
                devdata[j]['EcNo'] = 'N/A'
# NR
            if idxnr >0: # if NR  found
                if get_value_from_string(SS[j][idxnr], 'ssRsrp = ', ' '):
                    devdata[j]['ssRsrp'] = get_value_from_string(SS[j][idxnr], 'ssRsrp = ', ' ')
                else:
                    devdata[j]['ssRsrp'] = 'N/A'

                if get_value_from_string(SS[j][idxnr], 'ssRsrq = ', ' '):
                    devdata[j]['ssRsrq'] = get_value_from_string(SS[j][idxnr], 'ssRsrq = ', ' ')
                else:
                    devdata[j]['ssRsrq'] = 'N/A'

                if get_value_from_string(SS[j][idxnr], 'ssSinr = ', ' '):
                    devdata[j]['ssSinr'] = int(get_value_from_string(SS[j][idxnr], 'ssSinr = ', ' ')) / 10
                else:
                    devdata[j]['ssSinr'] = 'N/A'

# for Androidver =9
        elif intAndroidver <= 9:
            logger.debug('Android ver <= 9 =' + Androidver + 'from sss[] positions inflated ')
            if sss != []:
                if len(sss[j]) > 10:
                    if 'LTE' in Nettype[j]:
                        devdata[j]['mSS'] = 'NA'
                        if sss[j][8] != UNKNOWN_VALUE:
                            devdata[j]['mSS'] = sss[j][8]
                        else:
                            devdata[j]['mSS'] = 'N/A'
                        if sss[j][9] != UNKNOWN_VALUE:
                            devdata[j]['RSRP'] = sss[j][9]
                        else:
                            devdata[j]['RSRP'] = 'N/A'
                        if sss[j][10] != UNKNOWN_VALUE:
                            devdata[j]['RSRQ'] = sss[j][10]
                        else:
                            devdata[j]['RSRQ'] = 'N/A'
                        if sss[j][11] != UNKNOWN_VALUE:
                            devdata[j]['SINR'] = int(sss[j][11]) / 10
                        else:
                            devdata[j]['SINR'] = 'N/A'
                        if sss[j][12] != UNKNOWN_VALUE:
                            devdata[j]['CQI'] = sss[j][12]
                        else:
                            devdata[j]['CQI'] = 'N/A'
                    elif ('HSPA' in Nettype[j] or 'EDGE' in Nettype[j]):
                        devdata[j]['RSSI'] = 'NA'
                        if sss[j][3] != UNKNOWN_VALUE:
                            devdata[j]['mSS'] = sss[j][1]
                        else:
                            devdata[j]['mSS'] = 'N/A'
                        if sss[j][4] != UNKNOWN_VALUE:
                            devdata[j]['BER'] = int(sss[j][2])
                        else:
                            devdata[j]['BER'] = 'N/A'
                    elif 'GSM' in Nettype[j]:
                        devdata[j]['RSSI'] = 'NA'
                        if sss[j][1] != UNKNOWN_VALUE:
                            devdata[j]['mSS'] = sss[j][1]
                        else:
                            devdata[j]['mSS'] = 'N/A'
                        if sss[j][2] != UNKNOWN_VALUE:
                            devdata[j]['BER'] = int(sss[j][2])
                        else:
                            devdata[j]['BER'] = 'N/A'
                # for Androidver <9
                if intAndroidver < 9:
                    logger.debug('Android ver <9 =' + Androidver + 'ServStates processing')
                    if len(ServStates[j][13]) > 6:  # must be shortnames
                        devdata[j]['RTech'] = Nettype[j]
                        devdata[j]['mRATC'] = Nettype[j]
                    else:
                        devdata[j]['RTech'] = ServStates[j][13]
                        devdata[j]['mRATC'] = ServStates[j][14]
                    if 'mDataOperatorAlphaLong' in ServStates[j][6]:
                        devdata[j]['mCNOp'] = get_value_from_string(procdata[0][j], 'OperatorAlphaLong=', ',')
                    else:
                        if ServStates[j][6] != '':
                            devdata[j]['mCNOp'] = ServStates[j][6]  # NetOps
                        else:
                            ServStates[j][6] = NetOps[j]
                    if get_state(ServStates[j][0]):
                        devdata[j]['mRegCS'] = get_state(ServStates[j][0])
                        if 'IN_SERVICE' in devdata[j]['mRegCS']:
                            devdata[j]['mPLMN'] = NetPLMNs[j]
                    else:
                        devdata[j]['mRegCS'] = get_value_from_string(procdata[0][j], 'mVoiceRegState=', ',')[1:]
                    if get_state(ServStates[j][1]):
                        devdata[j]['mRegPS'] = get_state(ServStates[j][1])
                    else:
                        devdata[j]['mRegPS'] = get_value_from_string(procdata[0][1], 'mDataRegState=', ',')[1:]
# Android 9:
# ===========             GSM=   CDMA==    ==EvDO===  ========LTE========       =======?????===========
#    mSignalStrength=    1  2   3    4    5    6   7 8    9   10  11 12        13  14      15 16  17
# 	SignalStrength: 99 0 -120 -160 -120 -160 -1 20 -101 -13 124 2147483647 0 2147483647 99 255 2147483647 gsm|lte
# 	use_rsrp_and_rssnr_for_lte_level  [-120, -115, -110, -105, -97] [-115, -105, -95, -85]
#                                              1    2     3     4    5      6     7     8   9
# 
#                        gsm=   =cdma=    =Evdo===== =============LTE======================         =???=====
# Android 6.0.1		1  2   3    4    5    6   7 8    9        10         11       12           13
# 	SignalStrength: 99 0 -120 -160 -120   -1 -1 29  -83       -8         256      2147483647   2147483647  gsm|lte
# 	SignalStrength: 0  0 -120 -160 -120   0  -1 0 2147483647  2147483647 0        0            2147483647  gsm|lte
# Android 6.0.1		1  2   3    4    5    6   7 8    9        10         11       12           13
# 
# 
# 					         lte  lte  lte       lte
# >>> SS[0]                                        rsrp rsrq sinr*10   CQI
# ['SignalStrength: 99 0 -120 -160 -120 -160 -1 21 -102 -14  178       2147483647      0 2147483647 99 255 2147483647
#                  1  2   3    4    5    6   7 8    9   10   11       12             13  14        15 16  17
# 
# 
# gsm|lte use_rsrp_and_rssnr_for_lte_level  [-120, -115, -110, -105, -97] [-115, -105, -95, -85]\n    ']
# 
# 					         lte  lte  lte
#                                                 rsrp rsrq sinr*10
# >>> SS[1]
# ['SignalStrength: 99 0 -120 -160 -120 -160 -1 28  -85  -8  242  2147483647 0 2147483647 99 255 2147483647
#                  1  2   3    4    5    6   7 8    9   10   11       12             13  14        15 16  17
# 
# gsm|lte use_rsrp_and_rssnr_for_lte_level  [-120, -115, -110, -105, -97] [-115, -105, -95, -85]\n']
# Android <10:
#  mServiceState=0 0 voice home data home MegaFon MegaFon 25002 MegaFon MegaFon 25002  LTE LTE CSS not supported -1 -1 
#                | |                                                                                              |  |
#                c p
#                s s
# RoamInd=-1 DefRoamInd=-1 EmergOnly=false IsDataRoamingFromRegistration=false
#
#    0 --> IN_SERVICE
#    1 --> OUT_OF_SERVICE
#    2 --> EMERGENCY_ONLY
#    3 --> POWER_OFF
# 
#    public static final int STATE_EMERGENCY_ONLY
#    Добавлено в API уровня 1 Телефон зарегистрирован и заблокирован. Разрешены только номера экстренных служб.
#    Постоянное значение: 2 (0x00000002)
# 
#    public static final int STATE_IN_SERVICE
#    Добавлен в API level 1 Нормальное рабочее состояние, телефон зарегистрирован у оператора либо 
#                                                                   в домашней сети, либо в роуминге.
#    Постоянное значение: 0 (0x00000000)
# 
#    public static final int STATE_OUT_OF_SERVICE
#    Добавлено в API уровня 1 Телефон не зарегистрирован ни у одного оператора, 
#     телефон может в настоящее время искать нового оператора для регистрации или вообще не искать регистрацию,
#     или в регистрации отказано, или радиосигнал недоступен.
#    Постоянное значение: 1 (0x00000001)
# 
#    public static final int STATE_POWER_OFF
#    Добавлено в API уровня 1 Радио телефонии явно выключено.
#    Постоянное значение: 3 (0x00000003)
# 
#    Android ver <= 9 = 6.0.1
#    sss[0]:
#    0 SignalStrength:
#    1 99              GSM     mGsmSignalStrength
#    2 0               GSM     mGsmBitErrorRate
#    3 -120            CDMA    mCdmaDbm			-
#    4 -160            CDMA    mCdmaEcio			-
#    5 -120            EvDO    mEvdoDbm			-
#    6 -1              EvDO    mEvdoEcio
#    7 -1              EvDO    mEvdoSnr			-
#    8 28               LTE    mLteSignalStrength
#    9 -88              LTE    mLteRsrp
#    10 -11             LTE    mLteRsrq
#    11 220             LTE    mLteRssnr*10
#    12 2147483647      LTE    mLteCqi
#    13 2147483647      ???    ????????
#    14 gsm|lte
#    15
#    16
#    sss[1]:
#    0 SignalStrength:
#    1 0
#    2 0
#    3 -120
#    4 -160
#    5 -120
#    6 0
#    7 -1
#    8 0
#    9 2147483647
#    10 2147483647
#    11 0
#    12 0
#    13 2147483647
#    14 gsm|lte

        # if not Measonly:  # Full procedure Connection, not Measurememt only
        devdata[0]['WiFi_SSID'] = get_value_from_string(procdata[7][0], 'SSID:', ',')
        if get_value_from_string(procdata[7][0], 'Wifi Generation:', ','):
            devdata[0]['WiFi_Generation'] = get_value_from_string(procdata[7][0], 'Wifi Generation:', ',')
        else:
            devdata[0]['WiFi_Generation'] = get_value_from_string(procdata[7][0], 'Wi-Fi standard:', ',')
        devdata[0]['WiFi_link_speed'] = get_value_from_string(procdata[7][0], 'Link speed:', ',')
        devdata[0]['WiFi_TX_link_speed'] = get_value_from_string(procdata[7][0], 'Tx Link speed:', ',')
        devdata[0]['WiFi_RX_link_speed'] = get_value_from_string(procdata[7][0], 'Rx Link speed:', ',')
        devdata[0]['wRSSI'] = get_value_from_string(procdata[7][0], 'RSSI:', ',')
        if len(devdata) > 1: # RMq >1?
            devdata[1]['WiFi_SSID'] = get_value_from_string(procdata[7][0], 'SSID:', ',')
            if get_value_from_string(procdata[7][0], 'Wifi Generation:', ','):
                devdata[1]['WiFi_Generation'] = get_value_from_string(procdata[7][0], 'Wifi Generation:', ',')
            else:
                devdata[1]['WiFi_Generation'] = get_value_from_string(procdata[7][0], 'Wi-Fi standard:', ',')
            devdata[1]['WiFi_link_speed'] = get_value_from_string(procdata[7][0], 'Link speed:', ',')
            devdata[1]['WiFi_TX_link_speed'] = get_value_from_string(procdata[7][0], 'Tx Link speed:', ',')
            devdata[1]['WiFi_RX_link_speed'] = get_value_from_string(procdata[7][0], 'Rx Link speed:', ',')
            devdata[1]['wRSSI'] = get_value_from_string(procdata[7][0], 'RSSI:', ',')

        if not Measonly:  # Full procedure Connection, not Measurememt only
            if not get_value_from_string(procdata[7][1], 'Wi-Fi is ', '\n'):
                devdata[0]['WiFiConn'] = get_value_from_string(procdata[7][1], 'WifiState', '\n') # 'Current wifi mode:'
            else:
                devdata[0]['WiFiConn'] = get_value_from_string(procdata[7][1], 'Wi-Fi is ', '\n')
            if len(devdata) > 1: # ADB connected
                devdata[1]['WiFiConn'] = devdata[0]['WiFiConn']
            for i in range(len(procdata[6])):
                if 'wlan0' in procdata[6][i]:
                    devdata[0]['wIP'] = wip
                    devdata[0]['wIF'] = wif
                    if len(devdata) > 1:
                        devdata[1]['wIP'] = wip
                        devdata[1]['wIF'] = wif
                    break


def ADB_signal_output():
    """
    This procedure is for data output to console and to app list&table:
    Input: none
    Output: global vars:
    tv1_lst1        - 1st column of table#1 (RM#1 meas data)
    tv1_lst2        - 2nd column of table#1 (RM#1 meas data)
    tv1_lst3        - 3rd column of table#1 (RM#1 meas data)
    tv2_lst1        - 1st column of table#1 (RM#1 meas data)
    tv2_lst2        - 2nd column of table#1 (RM#1 meas data)
    tv2_lst3        - 3rd column of table#1 (RM#1 meas data)
    """
    logger.debug('---------------: call ADB_signal_output')
    global tv1_lst1, tv1_lst2, tv1_lst3, tv2_lst1, tv2_lst2, tv2_lst3

    j = 0  # RadioModule #1
    for b in dict.keys(devdata[j]):
        # table display and attenuation for radio LEVELS only
        if str(b) in LEVELS:
            tv1_lst1.append(str(b))
            tv1_lst2.append(devdata[j][b])
            tv1_lst3.append('----')
    if RMq > 1:
        j = 1  # RadioModule #2
        for b in dict.keys(devdata[j]):
            # table display and attenuation for radio LEVELS only
            if str(b) in LEVELS:
                tv2_lst1.append(str(b))
                tv2_lst2.append(devdata[j][b])
                tv2_lst3.append('----')

def print_devdata_to_console():
# devdata print to console
    print()
    print(f'Connected device: {DevMan} {DevDev} {DevMod} [{DevName} {DevName1}]')
    print('Android version:', Androidver)
    print('=============================')
    for j in range(RMq):
        print('Radio Module = ', j, ':')
        print('-----------------------------')
        for b in dict.keys(devdata[j]):
            print(b, ' = ', devdata[j][b])
        print()


def fill_devdata_to_l1(nr_support):
# devdata fill to lst_l1
    lst_l1[0] = f'Connected: {DevMan} {DevDev} {DevMod} [{DevName} {DevName1}]'
    lst_l1.append(f'Device S/N = {Device_SN}. Supported ABI: {abi_list}.')
    lst_l1.append(f'NR {nr_support}. Android version: {Androidver}, SDK level {SDK_ver}')
    if sim_state[0] == 'LOADED':
        simstat = colored_text(sim_state[0], col_val='#008000',weight=800)
    else:
        simstat = colored_text(sim_state[0], col_val='#800000', weight=500)
    lst_l1.append(f'Radio Module #1: SIM card:{simstat}')
    lst_l1.append(f'IMSI:{imsi[0]}, IMEI:{imei[0]}, MSISDN:{isdn[0]}')
    j = 0  # RadioModule #1
    for b in dict.keys(devdata[j]):
        if str(b) not in LEVELS:
            lst_l1.append(str(b) + ' = ' + str(devdata[j][b]))


def fill_devdata_to_l2(nr_support):
    # devdata fill to lst_l2
    if RMq > 1:
        lst_l2[0] = f'Connected: {DevMan} {DevDev} {DevMod} [{DevName} {DevName1}]'
        lst_l2.append(f'Device S/N = {Device_SN}. Supported ABI: {abi_list}.')
        lst_l2.append(f'NR {nr_support}. Android version: {Androidver}, SDK level {SDK_ver}')
        state = 'NONE' if len(sim_state[1])<2 else sim_state[1]
        if state == 'LOADED':
            simstat = colored_text(sim_state[1], col_val='#008000', weight=800)
        else:
            simstat = colored_text(sim_state[1], col_val='#800000', weight=500)
        lst_l2.append(f'Radio Module #2: SIM card:{simstat}')
        lst_l2.append(f'IMSI:{imsi[1]}, IMEI:{imei[1]}, MSISDN:{isdn[1]}')
        j = 1  # RadioModule #2
        for b in dict.keys(devdata[j]):
            if str(b) not in LEVELS:
                lst_l2.append(str(b) + ' = ' + str(devdata[j][b]))


def ADB_device_output():
    """
    This procedure is for data output to console and to app list&table:
    Input: none
    Output: global vars:
    lst_l1          - list1 (RM#1 connection) data
    lst_l2          - list2 (RM#2 connection) data
    """
    logger.debug('---------------: call ADB_device_output')
    global lst_l1, lst_l2
    print_devdata_to_console()

    if idxnr:
        nr_support = 'SUPPORTED'
    else:
        nr_support = 'is NOT supported'

    fill_devdata_to_l1(nr_support)
    fill_devdata_to_l2(nr_support)




############################################################################################
#    QtWidgets.qApp.processEvents() # Cycle Renew

############################################################################################
# Main. Functions()

def fill_device_memory_main():
    logger.debug('---------------: call FillMemory_main')


def clear_device_memory_main():
    logger.debug('---------------: call ClearMemory_main')


def switch_wifi_on_main():
    logger.debug('---------------: call WiFiOn_main')
# adb shell svc wifi enable
    parm = ' shell svc wifi enable'
    p = (subprocess.run(torun + parm, capture_output=True, text=True, shell=True))
    # procdata.append(p.stdout) >>>> ???????????????? why???????????????????????
    if len(p.stdout) > 2:
        logger.debug(p.stdout)


############################################################################################
# Main. Functions()


def switch_wifi_off_main():
    logger.debug('---------------: call WiFiOff_main')
    # adb shell svc wifi disable
    parm = ' shell svc wifi disable'  
    p = (subprocess.run(torun + parm, capture_output=True, text=True, shell=True))
    # procdata.append(p.stdout) ???????????????????????????? WHY ????????????????????
    if len(p.stdout) > 2:
        logger.debug(p.stdout)


def switch_mobile_data_on_main():
    logger.debug('---------------: call MobDataOn_main')
    # adb shell svc data enable
    parm = ' shell svc data enable'  
    p = (subprocess.run(torun + parm, capture_output=True, text=True, shell=True))
    # procdata.append(p.stdout) ????????????????????????????????????????????
    if len(p.stdout) > 2:
        logger.debug(p.stdout)


def switch_mobile_data_off_main():
    logger.debug('---------------: call MobDataOff_main')
    # adb shell svc data disable
    parm = ' shell svc data disable'  
    p = (subprocess.run(torun + parm, capture_output=True, text=True, shell=True))
    # procdata.append(p.stdout)???????????????????????????????????????????????????
    if len(p.stdout) > 2:
        logger.debug(p.stdout)


def display_settings_main():
    logger.debug('---------------: call DisplaySettings_main')
    # adb shell am start -a android.settings.SETTINGS
    parm = ' shell am start -a android.settings.SETTINGS'  # |grep '
    p = (subprocess.run(torun + parm, capture_output=True, text=True, shell=True))
    # procdata.append(p.stdout) ????????????????????????????????????????????????????????????????
    if len(p.stdout) > 2:
        logger.debug(p.stdout)

############################################################################################
# Main. Functions()


def connect_attenuator_main(ip: str):  #  unusable
    logger.debug('---------------: call AttenuatorConnect_main to ' + ip)
    pass

def disconnect_attenuator_main(ip: str):  # unusable
    logger.debug('---------------: call AttenuatorDisconnect_main to ' + ip)
    pass


def ssh_connect_main(ip: str, sshport: str, sshname: str, sshpwd: str):
    """Connect to ip:sshport SSH server 
    Args:
        ip (str): SSH IP address
        sshport (str): SSH port
        sshname (str): SSH User name
        sshpwd (str): SSH password
    Returns:
        (Bool): Result ( successfull or not)
        ['']: list of std.out + list of std.err
    """
    logger.debug('---------------: call sshConnect_main to ' + ip + ' : ' + str(sshport))
    p = ['']  # list with log strings
    b1 = connect_ssh(ip, sshport, sshname, sshpwd)
    if b1:
        [b2, p1] = check_ssh_Connect()
        p.extend(p1)
        if b2:
            logger.debug('---------------: sshConnect_main successfull')
            return True, p
    logger.error('---------------: sshConnect_main failed')
    return False, p


def ssh_disconnect_main(ip: str):
    p = []
    logger.debug('---------------: call sshDisconnect_main from ' + ip)
    p1 = disconnect_ssh()  # =========================================> Disconnect SSH server
    p.extend(p1)
    # +++ Kill last iperf server instance???
    logger.debug('---------------: SSH disconnected')
    return p

############################################################################################
############################################################################################
############################################################################################

LG_STYLE = """
QProgressBar{
    border: 2px solid grey;
    border-radius: 5px;
    text-align: center
}
QProgressBar::chunk {
    background-color: lightgreen;
    width: 10px;
    margin: 0px;
}
"""

LB_STYLE = """
QProgressBar{
    border: 2px solid grey;
    border-radius: 5px;
    text-align: center
}
QProgressBar::chunk {
    background-color: lightblue;
    width: 10px;
    margin: 0px;
}
"""

DEF_STYLE = """
QProgressBar{
    border: 2px solid grey;
    border-radius: 5px;
    # text-align: center
}
QProgressBar::chunk {
    background-color: darkgreen;
    width: 10px;
    margin: 0px;
}
"""
MY_STYLE = '''
QProgressBar{
    border: 1px solid grey;
    border-radius: 1px;
    # text-align: center
}
QProgressBar:: chunk{
    # background-color: #009688;
    background-color: lightblue;
    max-height: 12px;
    min-height: 12px;
    width: 10px;
    margin: 0px;
''' 


class MyProgressBar(QtWidgets.QProgressBar):
    def __init__(self, parent = None):
        QtWidgets.QProgressBar.__init__(self, parent)
        self.setStyleSheet(LB_STYLE)

    def setValue(self, value):
        QtWidgets.QProgressBar.setValue(self, value)

        if value == self.maximum():
            self.setStyleSheet(LG_STYLE)


class Communicate(QtCore.QObject):
    breakiperf = QtCore.pyqtSignal()

############################################################################################
# class Ui_MainWindow:

class Ui_MainWindow(object):

    def setupUi(self, MainWindow):
        MainWindow.setObjectName("MainWindow")
        MainWindow.resize(1056, 804)

        QToolTip.setFont(QFont('SansSerif', 9))
        self.setToolTip('ADB testing tool!')  # common Tooltip for all objects without own tooltips
        self.centralwidget = QtWidgets.QWidget(MainWindow)
        self.centralwidget.setObjectName("centralwidget")
#########
        self.progressBar_ADB = MyProgressBar(self.centralwidget)
        self.progressBar_ADB.setGeometry(QtCore.QRect(950, 32, 100, 16))
        self.progressBar_ADB.setMouseTracking(False)
        self.progressBar_ADB.setAcceptDrops(False)
        self.progressBar_ADB.setProperty("value", 0)  # same as reset
        self.progressBar_ADB.reset()
        self.progressBar_ADB.setObjectName("progressBar_ADB")

        self.toolButton_Connect_ADB = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_Connect_ADB.setGeometry(QtCore.QRect(867, 31, 80, 19))
        self.toolButton_Connect_ADB.setObjectName("toolButton_Connect_ADB")
        self.toolButton_Connect_ADB.setToolTip('Connect to UE via ADB')
        self.toolButton_Connect_ADB.setStyleSheet('background : #f0f0f0')
#########
        self.toolButton_PKGinstall = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_PKGinstall.setGeometry(QtCore.QRect(877, 91, 151, 19))
        self.toolButton_PKGinstall.setObjectName("toolButton_PKGinstall")
        self.toolButton_PKGinstall.setToolTip('Select PKG to be installed')
        self.toolButton_PKGinstall.setStyleSheet('background : #f0f0f0')

        self.toolButton_APKinstall = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_APKinstall.setGeometry(QtCore.QRect(877, 111, 151, 19))
        self.toolButton_APKinstall.setObjectName("toolButton_APKinstall")
        self.toolButton_APKinstall.setToolTip('Select APK to be installed')
        self.toolButton_APKinstall.setStyleSheet('background : #f0f0f0')

        self.toolButton_Meas = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_Meas.setGeometry(QtCore.QRect(877, 141, 81, 19))
        self.toolButton_Meas.setStyleSheet('font-weight: 600; color: #000000; font-size: 8pt;')
        self.toolButton_Meas.setObjectName("toolButton_Meas")
        self.toolButton_Meas.setToolTip('Signal Measurement')
        self.checkBox_meas = QtWidgets.QCheckBox(self.centralwidget)
        self.checkBox_meas.setTristate(True)
        self.checkBox_meas.setGeometry(QtCore.QRect(962, 141, 80, 17))
        self.checkBox_meas.setText("Continous")
        self.checkBox_meas.setObjectName("checkBox_meas")
        self.checkBox_meas.setToolTip('Continously: no/3s/1s')

        self.toolButton_MemFill = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_MemFill.setGeometry(QtCore.QRect(877, 171, 75, 19))
        self.toolButton_MemFill.setObjectName("toolButton_MemFill")
        self.toolButton_MemFill.setToolTip('Load all the memory of the UE')
        self.toolButton_MemFill.setStyleSheet('background : #f0f0f0')

        self.toolButton_MemClean = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_MemClean.setGeometry(QtCore.QRect(954, 171, 75, 19))
        self.toolButton_MemClean.setObjectName("toolButton_MemClean")
        self.toolButton_MemClean.setToolTip('Clear loaded memory of the UE')
        self.toolButton_MemClean.setStyleSheet('background : #f0f0f0')

        self.toolButton_WF_On = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_WF_On.setGeometry(QtCore.QRect(877, 191, 75, 19))
        self.toolButton_WF_On.setObjectName("toolButton_WF_On")
        self.toolButton_WF_On.setToolTip('Enable WiFi connection at the UE')
        self.toolButton_WF_On.setStyleSheet('background : #f0f0f0')

        self.toolButton_WF_Off = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_WF_Off.setGeometry(QtCore.QRect(954, 191, 75, 19))
        self.toolButton_WF_Off.setObjectName("toolButton_WF_Off")
        self.toolButton_WF_Off.setToolTip('Disable WiFi connection at the UE')
        self.toolButton_WF_Off.setStyleSheet('background : #f0f0f0')

        self.toolButton_MD_On = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_MD_On.setGeometry(QtCore.QRect(877, 211, 75, 19))
        self.toolButton_MD_On.setObjectName("toolButton_MD_On")
        self.toolButton_MD_On.setToolTip('Enable Mobile Data connection at the UE')
        self.toolButton_MD_On.setStyleSheet('background : #f0f0f0')

        self.toolButton_MD_Off = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_MD_Off.setGeometry(QtCore.QRect(954, 211, 75, 19))
        self.toolButton_MD_Off.setObjectName("toolButton_MD_Off")
        self.toolButton_MD_Off.setToolTip('Disable Mobile Data connection at the UE')
        self.toolButton_MD_Off.setStyleSheet('background : #f0f0f0')

        self.toolButton_DispSettings = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_DispSettings.setGeometry(QtCore.QRect(877, 231, 151, 19))
        self.toolButton_DispSettings.setObjectName("toolButton_DispSettings")
        self.toolButton_DispSettings.setToolTip('Call Settings menu at the UE')
        self.toolButton_DispSettings.setStyleSheet('background : #f0f0f0')

# SSH server Connection
        self.comboBox_3 = QtWidgets.QComboBox(self.centralwidget)
#        self.comboBox_3.setStyleSheet('background : #f0f0f0; font-weight: 400; color: darkblue; font-size:8pt;')
        self.comboBox_3.setStyleSheet('background : #f0f0f0; font-weight: 400;')
        self.comboBox_3.setGeometry(QtCore.QRect(950, 305, 100, 19))
        self.comboBox_3.setObjectName("comboBox_3_ssh_server_choice")
        self.comboBox_3.setToolTip('Choose predefined SSH server from list')
        self.comboBox_3.setObjectName("SSH servers list")
# 'SSH servers list'
        self.label_18 = QtWidgets.QLabel(self.centralwidget)
        self.label_18.setGeometry(QtCore.QRect(955, 291, 100, 12))
#        self.label_18.setStyleSheet('font-weight: 500; color: #0505b5; font-size: 8pt;')
        self.label_18.setStyleSheet('font-weight: 500; ')
        self.label_18.setObjectName("label_18")
        for i in range(len(servers)):
            self.comboBox_3.addItem(servers[i][1])  # names
        self.comboBox_3.addItem('                  ') #latest record

        self.progressBar_ssh = MyProgressBar(self.centralwidget)
        self.progressBar_ssh.setGeometry(QtCore.QRect(960, 351, 93, 15))
        self.progressBar_ssh.setProperty("value", 0)
        self.progressBar_ssh.setObjectName("progressBar_ssh")

        # iperf3 base port ( iperf2 tcp +=10, iperf2 udp +=20)
        self.lineEdit_iperf_port = QtWidgets.QLineEdit(str(IPERF3_PORT), self.centralwidget)
        self.lineEdit_iperf_port.setGeometry(QtCore.QRect(880, 265, 40, 20))
        self.lineEdit_iperf_port.setObjectName("iperf3 base port")
        # self.lineEdit_iperf_port.setValidator(int_Validator)
        self.lineEdit_iperf_port.setToolTip('iperf3 base port')
        self.lineEdit_iperf_port.setStyleSheet('font-weight: 500; color: #0505b5; font-size: 8pt;')

        self.label_iperf_port = QtWidgets.QLabel(self)
        self.label_iperf_port.setGeometry(925, 260, 400, 30)
        self.label_iperf_port.setText("iperf base port")

# iperf2//iperf3 radio button
        self.iperf2_button = QtWidgets.QRadioButton(self)
        self.iperf2_button.setGeometry(880, 280, 80, 40)
        self.iperf2_button.setText("iperf2")

        self.iperf3_button = QtWidgets.QRadioButton(self)
        self.iperf3_button.setGeometry(880, 300, 80, 40)
        self.iperf3_button.setText("iperf3")

# SSH Connection/disconnection
        self.toolButton_Connect_ssh = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_Connect_ssh.setGeometry(QtCore.QRect(867, 410, 80, 19))
        self.toolButton_Connect_ssh.setObjectName("toolButton_Connect_ssh")
        self.toolButton_Connect_ssh.setStyleSheet('background : #f0f0f0')

        self.toolButton_Disconnect_ssh = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_Disconnect_ssh.setGeometry(QtCore.QRect(960, 410, 80, 19))
        self.toolButton_Disconnect_ssh.setObjectName("toolButton_Disconnect_ssh")
        self.toolButton_Disconnect_ssh.setStyleSheet('background : #f0f0f0')

        ipRange = "(?:[0-1]?[0-9]?[0-9]|2[0-4][0-9]|25[0-5])"   # 1 Octet = part of regex
        # full regex of 4 x octets:
        ipRegex = QRegExp("^" + ipRange + "\\." + ipRange + "\\." + ipRange + "\\." + ipRange + "$")
        ipValidator = QRegExpValidator(ipRegex, self)   # Validator for Att_IP & SSH QLineEdit

        self.lineEdit_ssh_IP = QtWidgets.QLineEdit("10.10.30.3", self.centralwidget)
        self.lineEdit_ssh_IP.setStyleSheet('background : #00001f; font-weight: 500; color: #d5d5d5; font-size: 7pt;')
        self.lineEdit_ssh_IP.setGeometry(QtCore.QRect(867, 350, 80, 20))
        self.lineEdit_ssh_IP.setObjectName("lineEdit_ssh_IP")
        self.lineEdit_ssh_IP.setValidator(ipValidator)      # set IP Validator 
        self.lineEdit_ssh_IP.setToolTip('SSH server IP address')

        self.lineEdit_ssh_Uname = QtWidgets.QLineEdit("username", self.centralwidget)
        self.lineEdit_ssh_Uname.setStyleSheet('background : #f0f0f0; font-weight: 300; color: blue; font-size:8pt;')
        self.lineEdit_ssh_Uname.setGeometry(QtCore.QRect(867, 385, 80, 20))
        self.lineEdit_ssh_Uname.setObjectName("lineEdit_ssh_Uname")
        self.lineEdit_ssh_Uname.setToolTip('SSH server User Name')

        self.lineEdit_ssh_Pwd = QtWidgets.QLineEdit("password", self.centralwidget)
        self.lineEdit_ssh_Pwd.setStyleSheet('background : #f0f0f0; font-weight: 300; color: blue; font-size:8pt;')
        self.lineEdit_ssh_Pwd.setGeometry(QtCore.QRect(960, 385, 80, 20))
        self.lineEdit_ssh_Pwd.setObjectName("lineEdit_ssh_Pwd")
        self.lineEdit_ssh_Pwd.setToolTip('SSH server password')

        self.c = Communicate()
        self.c.breakiperf.connect(self.break_action)

# "SSH server IP"
        self.label_14 = QtWidgets.QLabel(self.centralwidget)
        self.label_14.setGeometry(QtCore.QRect(870, 333, 71, 16))
        self.label_14.setObjectName("label_14")
# "Iperf SSH server"
        self.label_15 = QtWidgets.QLabel(self.centralwidget)
        self.label_15.setGeometry(QtCore.QRect(960, 331, 111, 16))
        self.label_15.setObjectName("label_15")
# "SSH server UserName"
        self.label_16 = QtWidgets.QLabel(self.centralwidget)
        self.label_16.setGeometry(QtCore.QRect(870, 368, 71, 16))
        self.label_16.setObjectName("label_16")
# "SSH server Pwd"
        self.label_17 = QtWidgets.QLabel(self.centralwidget)
        self.label_17.setGeometry(QtCore.QRect(960, 368, 71, 16))
        self.label_17.setObjectName("label_17")

# IPERF measurements
        self.toolButton_tcp_UL_tpt = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_tcp_UL_tpt.setGeometry(QtCore.QRect(867, 440, 80, 19))
        self.toolButton_tcp_UL_tpt.setObjectName("toolButton_tcp_UL_tpt")
        self.toolButton_tcp_UL_tpt.setStyleSheet('background : #f0f0f0')

        self.toolButton_tcp_DL_tpt = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_tcp_DL_tpt.setGeometry(QtCore.QRect(867, 460, 80, 19))
        self.toolButton_tcp_DL_tpt.setObjectName("toolButton_tcp_DL_tpt")
        self.toolButton_tcp_DL_tpt.setStyleSheet('background : #f0f0f0')

        self.toolButton_tcp_bidi_tpt = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_tcp_bidi_tpt.setGeometry(QtCore.QRect(960, 460, 72, 19))
        self.toolButton_tcp_bidi_tpt.setObjectName("toolButton_tcp_bidi_tpt")
        self.toolButton_tcp_bidi_tpt.setStyleSheet('background : #f0f0f0')

        self.toolButton_udp_UL_tpt = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_udp_UL_tpt.setGeometry(QtCore.QRect(867, 505, 80, 19))
        self.toolButton_udp_UL_tpt.setObjectName("toolButton_udp_UL_tpt")
        self.toolButton_udp_UL_tpt.setStyleSheet('background : #f0f0f0')

        self.toolButton_udp_DL_tpt = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_udp_DL_tpt.setGeometry(QtCore.QRect(867, 525, 80, 19))
        self.toolButton_udp_DL_tpt.setObjectName("toolButton_udp_DL_tpt")
        self.toolButton_udp_DL_tpt.setStyleSheet('background : #f0f0f0')

        self.toolButton_udp_bidi_tpt = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_udp_bidi_tpt.setGeometry(QtCore.QRect(960, 525, 72, 19))
        self.toolButton_udp_bidi_tpt.setObjectName("toolButton_udp_bidi_tpt")
        self.toolButton_udp_bidi_tpt.setStyleSheet('background : #f0f0f0')

# checkbox for --forceflush addition (iperf3) // --enhance option (iperf2)
        self.checkBox_flush = QtWidgets.QCheckBox(self.centralwidget)
        # self.checkBox_flush.setTristate(True)
        self.checkBox_flush.setGeometry(QtCore.QRect(880, 485, 70, 17))
        self.checkBox_flush.setText("Flush")
        self.checkBox_flush.setObjectName("forceflush")
        self.checkBox_flush.setToolTip('--forceflush, iperf3 only')

# break iperf button
        self.toolButton_break = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_break.setGeometry(QtCore.QRect(940, 482, 29, 19))
        self.toolButton_break.setObjectName("break")
        self.toolButton_break.setText("br")
        self.toolButton_break.setStyleSheet('background : #f0f0f0; font-weight: 400; color: darkred; font-size:8pt;')

        # checkbox for summary addition ("| grep SUM")
        self.checkBox_sum = QtWidgets.QCheckBox(self.centralwidget)
        # self.checkBox_flush.setTristate(True)
        self.checkBox_sum.setGeometry(QtCore.QRect(980, 485, 70, 17))
        self.checkBox_sum.setText("Sum")
        self.checkBox_sum.setObjectName("summary")
        self.checkBox_sum.setToolTip('summary')
        self.checkBox_sum.setChecked(True)  # set checked by default

        # Regex filter for digits only (seconds, threads, Mbps)
        int_Regex = QRegExp("^(\d+)$")
        int_Validator = QRegExpValidator(int_Regex, self)  # Validator for Att_Channel QLineEdit

# tcp duration -t
        self.lineEdit_iperf_tcp_time = QtWidgets.QLineEdit("3", self.centralwidget)
        self.lineEdit_iperf_tcp_time.setGeometry(QtCore.QRect(960, 440, 35, 20))
        self.lineEdit_iperf_tcp_time.setObjectName("iperf tcp session time")
        self.lineEdit_iperf_tcp_time.setValidator(int_Validator)
        self.lineEdit_iperf_tcp_time.setToolTip('iperf tcp session time')

# tcp threads -P
        self.lineEdit_iperf_tcp_sessions = QtWidgets.QLineEdit("1", self.centralwidget)
        self.lineEdit_iperf_tcp_sessions.setGeometry(QtCore.QRect(996, 440, 35, 20))
        self.lineEdit_iperf_tcp_sessions.setObjectName("iperf tcp sessions")
        self.lineEdit_iperf_tcp_sessions.setValidator(int_Validator)
        self.lineEdit_iperf_tcp_sessions.setToolTip('iperf tcp parallel sessions')

# udp duration -t
        self.lineEdit_iperf_udp_time = QtWidgets.QLineEdit("3", self.centralwidget)
        self.lineEdit_iperf_udp_time.setGeometry(QtCore.QRect(960, 505, 35, 20))
        self.lineEdit_iperf_udp_time.setObjectName("iperf udp session time")
        self.lineEdit_iperf_udp_time.setValidator(int_Validator)
        self.lineEdit_iperf_udp_time.setToolTip('iperf udp session time')

# udp bandwith -B (Mbps)
        self.lineEdit_iperf_udp_bandwith = QtWidgets.QLineEdit("100", self.centralwidget)
        self.lineEdit_iperf_udp_bandwith.setGeometry(QtCore.QRect(996, 505, 35, 20))
        self.lineEdit_iperf_udp_bandwith.setObjectName("iperf udp bandwith")
        self.lineEdit_iperf_udp_bandwith.setValidator(int_Validator)
        self.lineEdit_iperf_udp_bandwith.setToolTip('iperf udp bandwith, Mbps')

# Attenuator Connection
        # self.progressBar_Att = QtWidgets.QProgressBar(self.centralwidget) # MyProgressBar
        self.progressBar_Att = MyProgressBar(self.centralwidget) 
        self.progressBar_Att.setGeometry(QtCore.QRect(867, 630, 110, 16))
        self.progressBar_Att.setProperty("value", 0)
        self.progressBar_Att.setObjectName("progressBar_Att")

        self.toolButton_Connect_Att = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_Connect_Att.setGeometry(QtCore.QRect(867, 696, 80, 19))
        self.toolButton_Connect_Att.setObjectName("toolButton_Connect_Att")
        self.toolButton_Connect_Att.setStyleSheet('background : #f0f0f0')

        self.toolButton_Disconnect = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_Disconnect.setGeometry(QtCore.QRect(957, 696, 80, 19))
        self.toolButton_Disconnect.setObjectName("toolButton_Disconnect")
        self.toolButton_Disconnect.setStyleSheet('background : #f0f0f0')

        self.toolButton_Clear_Att = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_Clear_Att.setGeometry(QtCore.QRect(867, 716, 80, 19))
        self.toolButton_Clear_Att.setObjectName("toolButton_att_clear")
        self.toolButton_Clear_Att.setStyleSheet('background : #f0f0f0')

        self.lineEdit_Att_IP = QtWidgets.QLineEdit("10.88.128.52", self.centralwidget)
        self.lineEdit_Att_IP.setGeometry(QtCore.QRect(867, 670, 80, 20))
        self.lineEdit_Att_IP.setStyleSheet('background : #00001f; font-weight: 500; color: #d5d5d5; font-size: 7pt;')
        self.lineEdit_Att_IP.setObjectName("lineEdit_Att_IP")
        self.lineEdit_Att_IP.setValidator(ipValidator)      # set IP Validator 
        self.lineEdit_Att_IP.setToolTip('Attenuator IP address')

        attChnlRegex = QRegExp("^(?:[1-9]||1[0-9]|2[0-4])(:|,|-)"
                               "(?:[1-9]||1[0-9]|2[0-4])(,)"
                               "(?:[1-9]||1[0-9]|2[0-4])(,)"
                               "(?:[1-9]||1[0-9]|2[0-4])$")
        ChnlValidator = QRegExpValidator(attChnlRegex, self)   # Validator for Att_Channel QLineEdit
        self.lineEdit_Att_Chn = QtWidgets.QLineEdit("1", self.centralwidget)
        self.lineEdit_Att_Chn.setGeometry(QtCore.QRect(957, 670, 71, 20))
        self.lineEdit_Att_Chn.setObjectName("lineEdit_Att_Chn")
        self.lineEdit_Att_Chn.setValidator(ChnlValidator)      # set Att channel Validator 
        self.lineEdit_Att_Chn.setToolTip('Attenuator channels, for example: 1-8,15,17')

# "Attenuator connection"
        self.label_10 = QtWidgets.QLabel(self.centralwidget)
        self.label_10.setGeometry(QtCore.QRect(867, 612, 150, 16))
        self.label_10.setObjectName("label_10")
# "Attenuator IP"
        self.label_4 = QtWidgets.QLabel(self.centralwidget)
        self.label_4.setGeometry(QtCore.QRect(869, 651, 121, 16))
        self.label_4.setObjectName("label_4")
# "Attenuator Channel"
        self.label_5 = QtWidgets.QLabel(self.centralwidget)
        self.label_5.setGeometry(QtCore.QRect(960, 651, 101, 16))
        self.label_5.setObjectName("label_5")

# DialogBox
        self.buttonBox = QtWidgets.QDialogButtonBox(self.centralwidget)
        self.buttonBox.setGeometry(QtCore.QRect(867, 740, 170, 20))
        self.buttonBox.setOrientation(QtCore.Qt.Horizontal)
        self.buttonBox.setStandardButtons(QtWidgets.QDialogButtonBox.Cancel | QtWidgets.QDialogButtonBox.Ok)
        self.buttonBox.setCenterButtons(True)
        self.buttonBox.setObjectName("buttonBox")

# "Radio Module#1 (sim card 1)"
        self.label_7 = QtWidgets.QLabel(self.centralwidget)
        self.label_7.setGeometry(QtCore.QRect(127, 361, 141, 16))
        self.label_7.setObjectName("label_7")
# "Radio Module#1 (sim card 2)"
        self.label_8 = QtWidgets.QLabel(self.centralwidget)
        self.label_8.setGeometry(QtCore.QRect(567, 361, 141, 16))
        self.label_8.setObjectName("label_8")
# "ADB connection"
        self.label_9 = QtWidgets.QLabel(self.centralwidget)
        self.label_9.setGeometry(QtCore.QRect(917, 11, 81, 16))
        self.label_9.setObjectName("label_9")
# ComboBoxes
        self.comboBox_1 = QtWidgets.QComboBox(self.centralwidget)
        self.comboBox_1.setGeometry(QtCore.QRect(3, 1, 85, 22))
        self.comboBox_1.setObjectName("comboBox_1")
        self.comboBox_1.addItem("")  # 0
        self.comboBox_1.addItem("")  # 1
        self.comboBox_1.addItem("")  # 2
        self.comboBox_1.addItem("")  # 3
        self.comboBox_1.addItem("")  # 4
        self.comboBox_1.addItem("")  # 5
        self.comboBox_1.addItem("")  # 6
        self.comboBox_1.addItem("")  # 7
        self.comboBox_1.addItem("")  # 8
        self.comboBox_1.addItem("")  # 9

# checkbox for List1 expanding
        self.checkBox_L1_exp = QtWidgets.QCheckBox(self.centralwidget)
        self.checkBox_L1_exp.setGeometry(QtCore.QRect(93, 3, 120, 17))
        self.checkBox_L1_exp.setText("expand window >>")
        self.checkBox_L1_exp.setObjectName("L1_expand")
        self.checkBox_L1_exp.setToolTip('expand window')

        self.comboBox_2 = QtWidgets.QComboBox(self.centralwidget)
        self.comboBox_2.setGeometry(QtCore.QRect(428, 1, 85, 22))
        self.comboBox_2.setObjectName("comboBox_2")
        self.comboBox_2.addItem("")  # 0
        self.comboBox_2.addItem("")  # 1
        self.comboBox_2.addItem("")  # 2
        self.comboBox_2.addItem("")  # 3
        self.comboBox_2.addItem("")  # 4
        self.comboBox_2.addItem("")  # 5
        self.comboBox_2.addItem("")  # 6
        self.comboBox_2.addItem("")  # 7
        self.comboBox_2.addItem("")  # 8
        self.comboBox_2.addItem("")  # 9

# clear L1 list bitton
        self.toolButton_clear_L1 = QtWidgets.QToolButton(self.centralwidget)
        self.toolButton_clear_L1.setGeometry(QtCore.QRect(205, 3, 29, 19))
        self.toolButton_clear_L1.setObjectName("cls")
        self.toolButton_clear_L1.setStyleSheet('background : #f0f0f0')

        # "Label Watchdog timer"
        self.label_watch = QtWidgets.QLabel(self.centralwidget)
        self.label_watch.setGeometry(QtCore.QRect(240, 3, 101, 16))
        self.label_watch.setObjectName("label_watch")
        self.label_watch.setText(f'Watchdog: {TIMEOUT_IPERF_CLIENT}s')
        self.label_watch.setHidden(True)


#####
# Status Bar & Menu Bar (centralwidget)
############################################################################################
        MainWindow.setCentralWidget(self.centralwidget)
        self.menubar = QtWidgets.QMenuBar(MainWindow)
        self.menubar.setGeometry(QtCore.QRect(0, 0, 1064, 21))
        self.menubar.setObjectName("menubar")
                
        MainWindow.setMenuBar(self.menubar)
        self.statusbar = QtWidgets.QStatusBar(MainWindow)
        self.statusbar.setObjectName("statusbar")
        MainWindow.setStatusBar(self.statusbar)
        ############################################################################################

        self.retranslateUi(MainWindow)
        QtCore.QMetaObject.connectSlotsByName(MainWindow)

############################################################################################
############################################################################################
# class Ui_MainWindow. Methods

    def retranslateUi(self, MainWindow):
        _translate = QtCore.QCoreApplication.translate
        MainWindow.setWindowTitle(_translate("MainWindow", "ADB Testing Tool"))
        self.toolButton_clear_L1.setText(_translate("MainWindow", "cls"))
        self.toolButton_Connect_ADB.setText(_translate("MainWindow", "C&onnect"))
        self.toolButton_PKGinstall.setText(_translate("MainWindow", "Install &Packages"))
        self.toolButton_APKinstall.setText(_translate("MainWindow", "Install set of &Apk"))
        self.toolButton_Meas.setText(_translate("MainWindow", "Signal &Meas."))
        self.toolButton_MemFill.setText(_translate("MainWindow", "Memory &Fill"))
        self.toolButton_MemClean.setText(_translate("MainWindow", "Memory c&Lean"))
        self.toolButton_MD_On.setText(_translate("MainWindow", "Mob.data O&N"))
        self.toolButton_MD_Off.setText(_translate("MainWindow", "Mob.data O&FF"))
        self.toolButton_WF_On.setText(_translate("MainWindow", "&WiFi On"))
        self.toolButton_WF_Off.setText(_translate("MainWindow", "W&iFi Off"))
        self.toolButton_DispSettings.setText(_translate("MainWindow", "Display &Settings screen"))

        self.toolButton_Disconnect.setText(_translate("MainWindow", "Att.Disconn."))
        self.toolButton_Connect_Att.setText(_translate("MainWindow", "Att.Connect"))
        self.toolButton_Disconnect_ssh.setText(_translate("MainWindow", "SSH Disconnect"))
        self.toolButton_Clear_Att.setText(_translate("MainWindow", "Clear Att."))
        self.toolButton_Connect_ssh.setText(_translate("MainWindow", "&SSH connect"))

        self.toolButton_tcp_UL_tpt.setText(_translate("MainWindow", "tcp &UL Tpt"))
        self.toolButton_tcp_DL_tpt.setText(_translate("MainWindow", "tcp &DL Tpt"))
        self.toolButton_tcp_bidi_tpt.setText(_translate("MainWindow", "tcp &BiDi Tpt"))

        self.toolButton_udp_UL_tpt.setText(_translate("MainWindow", "udp UL Tpt"))
        self.toolButton_udp_DL_tpt.setText(_translate("MainWindow", "udp DL Tpt"))
        self.toolButton_udp_bidi_tpt.setText(_translate("MainWindow", "udp BiDi Tpt"))

        self.label_4.setText(_translate("MainWindow", "Attenuator IP"))
        self.label_7.setText(_translate("MainWindow", "Radio Module#1 (sim card 1)"))
        self.label_8.setText(_translate("MainWindow", "Radio Module#2 (sim card 2)"))
        self.label_5.setText(_translate("MainWindow", "Att. Channels"))
        self.label_9.setText(_translate("MainWindow", "ADB connection"))
        self.label_10.setText(_translate("MainWindow", "Attenuator connection"))
        self.label_14.setText(_translate("MainWindow", "SSH server IP"))
        self.label_15.setText(_translate("MainWindow", "Iperf SSH server"))
        self.label_16.setText(_translate("MainWindow", "User Name"))
        self.label_17.setText(_translate("MainWindow", "Password"))
        self.label_18.setText(_translate("MainWindow", "SSH servers list"))


        self.comboBox_1.setItemText(0, _translate("MainWindow", "Connection"))
        self.comboBox_1.setItemText(1, _translate("MainWindow", "WiFi info"))
        self.comboBox_1.setItemText(2, _translate("MainWindow", "WiFi scanner"))
        self.comboBox_1.setItemText(3, _translate("MainWindow", "IP info"))
        self.comboBox_1.setItemText(4, _translate("MainWindow", "Battery info"))
        self.comboBox_1.setItemText(5, _translate("MainWindow", "Disk info"))
        self.comboBox_1.setItemText(6, _translate("MainWindow", "RAM info"))
        self.comboBox_1.setItemText(7, _translate("MainWindow", "pkg list"))
        self.comboBox_1.setItemText(8, _translate("MainWindow", "apk list"))
        self.comboBox_1.setItemText(9, _translate("MainWindow", "Iperf Client"))
        self.comboBox_1.setItemText(10, _translate("MainWindow", "--------"))

        self.comboBox_2.setItemText(0, _translate("MainWindow", "Connection"))
        self.comboBox_2.setItemText(1, _translate("MainWindow", "WiFi info"))
        self.comboBox_2.setItemText(2, _translate("MainWindow", "WiFi scanner"))
        self.comboBox_2.setItemText(3, _translate("MainWindow", "IP info"))
        self.comboBox_2.setItemText(4, _translate("MainWindow", "Battery info"))
        self.comboBox_2.setItemText(5, _translate("MainWindow", "Disk info"))
        self.comboBox_2.setItemText(6, _translate("MainWindow", "RAM info"))
        self.comboBox_2.setItemText(7, _translate("MainWindow", "pkg result"))
        self.comboBox_2.setItemText(8, _translate("MainWindow", "apk result"))
        self.comboBox_2.setItemText(9, _translate("MainWindow", "Iperf Server"))
        self.comboBox_2.setItemText(10, _translate("MainWindow", "--------"))
############################################################################################
############################################################################################
############################################################################################
# 3

############################################################################################
# class ADB_App_Main:


class ADB_App_Main(QtWidgets.QMainWindow, Ui_MainWindow):
    def __init__(self, *args, obj=None, **kwargs):
        # super(ADB_App_Main, self).__init__(*args, **kwargs)
        super().__init__(*args, **kwargs)
        self.setupUi(self)  # инициализация дизайна

        self.watchdog_type = True # Watchdog for iperf client run with Watchdog class, not with QTimer
        self.timer = QTimer(self)
        self.timer_iperf = QTimer(self)
        self.iperf_current_timeout_value = TIMEOUT_IPERF_CLIENT
        # self.thread = QtCore.QThread()
        # self.timer_iperf.moveToThread(self.thread)
        # self.thread.started.connect(self.timer_iperf.stop)
        # self.thread.start()

        self.whiteColor = QtGui.QColor(255, 255, 255, 127)
        self.lightgreenColor = QtGui.QColor(32, 255, 0, 127)
        self.lightredColor = QtGui.QColor(255, 0, 0, 127)
        self.greenyellowColor = QtGui.QColor(173, 255, 47, 127)
        self.yellowColor = QtGui.QColor(255, 255, 0, 127)


        self.pkginst = []  # list pkgs to be installed
        self.apkinst = []  # list apks to be installed
        self.iperfsrvrs2run = []  # list of  iperfs to run as daemons servers at SSH server

        self.iperf_srvr_log_lst = []  # server log list
        self.iperf_clnt_lst = []  # client log list
        self.wrong_input = False  # flag for return to main when error

        self.iperf3_button.setChecked(True) # initial value
        self.iperf_version = 3 # initial value
        self.iperf_break = False # signal for send SIGINT (break) to adb shell with iperf session
        self.lineEdit_iperf_port.editingFinished.connect(self.change_iperf_port)
        self.toolButton_break.pressed.connect(self.iperf_client_break)
        self.iperf2_button.pressed.connect(self.iperf2_version_chosen)
        self.iperf3_button.pressed.connect(self.iperf3_version_chosen)
        self.toolButton_clear_L1.pressed.connect(self.clearRecs_l1)  
        self.buttonBox.accepted.connect(self.ADB_device_connect)  # 'OK'
        self.buttonBox.rejected.connect(self.close)  # 'Cancel'
        self.toolButton_PKGinstall.pressed.connect(self.Install_pkg_set)
        self.toolButton_APKinstall.pressed.connect(self.Install_apk_set)
        self.toolButton_Connect_ADB.pressed.connect(self.ADB_device_connect)
        self.toolButton_Meas.pressed.connect(self.SignalMeasurement)
        self.toolButton_MemFill.pressed.connect(self.FillMemory)
        self.toolButton_MemClean.pressed.connect(self.ClearMemory)
        self.toolButton_WF_On.pressed.connect(self.WiFiOn)
        self.toolButton_WF_Off.pressed.connect(self.WiFiOff)
        self.toolButton_MD_On.pressed.connect(self.MobDataOn)
        self.toolButton_MD_Off.pressed.connect(self.MobDataOff)
        self.toolButton_DispSettings.pressed.connect(self.DisplaySettings)
        self.toolButton_Connect_Att.pressed.connect(self.AttenuatorConnect)
        self.toolButton_Disconnect.pressed.connect(self.AttenuatorDisconnect)
        self.toolButton_Connect_ssh.pressed.connect(self.sshConnect)
        self.toolButton_Disconnect_ssh.pressed.connect(self.sshDisconnect)
        self.toolButton_Clear_Att.pressed.connect(self.Atts_clear)

        self.toolButton_tcp_UL_tpt.pressed.connect(self.run_iperfclnt_tcp_UL)
        self.toolButton_tcp_DL_tpt.pressed.connect(self.run_iperfclnt_tcp_DL)
        self.toolButton_tcp_bidi_tpt.pressed.connect(self.run_iperfclnt_tcp_BiDi)

        self.toolButton_udp_UL_tpt.pressed.connect(self.run_iperfclnt_udp_UL)
        self.toolButton_udp_DL_tpt.pressed.connect(self.run_iperfclnt_udp_DL)
        self.toolButton_udp_bidi_tpt.pressed.connect(self.run_iperfclnt_udp_BiDi)

        self.comboBox_1.currentIndexChanged['QString'].connect(self.List1Update)
        self.comboBox_2.currentIndexChanged['QString'].connect(self.List2Update)
        self.comboBox_3.currentIndexChanged['QString'].connect(self.List3Update)
        self.checkBox_L1_exp.stateChanged.connect(self.List1Expand)
        self.checkBox_meas.stateChanged.connect(self.periodic_signal_measurement_main)
        self.timer.timeout.connect(self.update_func)
        self.timer_iperf.timeout.connect(self.periodic_iperf_client_timeout)


        # self.comboBox_1.setItemText(0, _translate("MainWindow", "Connection"))        0
        # self.comboBox_1.setItemText(1, _translate("MainWindow", "WiFi info"))         1
        # self.comboBox_1.setItemText(2, _translate("MainWindow", "WiFi scanner"))      2
        # self.comboBox_1.setItemText(3, _translate("MainWindow", "IP info"))           3
        # self.comboBox_1.setItemText(4, _translate("MainWindow", "Battery info"))      4
        # self.comboBox_1.setItemText(5, _translate("MainWindow", "Disk info"))         5
        # self.comboBox_1.setItemText(6, _translate("MainWindow", "RAM info"))          6
        # self.comboBox_1.setItemText(7, _translate("MainWindow", "pkg list"))          7
        # self.comboBox_1.setItemText(8, _translate("MainWindow", "apk list"))          8
        # self.comboBox_1.setItemText(9, _translate("MainWindow", "Iperf Client"))      9
        # self.comboBox_1.setItemText(10, _translate("MainWindow", "--------"))         10


    # Combobox Indexes:
        self.common_index = 0
        self.Winfo_index = 1  # Reserved yet
        self.Wscan_index = 2
        self.IP_index = 3
        self.battery_index = 4
        self.disk_index = 5
        self.RAM_index = 6
        self.pkg_index = 7
        self.apk_index = 8
        self.iperf_index = 9  # combobox_1=client, combobox_2=server
        self.reserved_index = 10  # Reserved
            
        self.comboBox_1.setCurrentIndex(self.common_index)

############################################################################################
############################################################################################
############################################################################################

        self.textEdit_1 = QtWidgets.QTextEdit(self)
        self.textEdit_1.setGeometry(QtCore.QRect(2, 22, 421, 341))
        self.textEdit_1.setObjectName("listView_1")
        self.textEdit_1.clear()
        self.textEdit_1.setFontFamily("Consolas")  # Lucida Console
      
        self.textEdit_2 = QtWidgets.QTextEdit(self)
        self.textEdit_2.setGeometry(QtCore.QRect(427, 22, 421, 341))
        self.textEdit_2.setObjectName("listView_2")
        self.textEdit_2.clear()
        self.textEdit_2.setFontFamily("Consolas")  # Lucida Console

# tableView_1
        self.tableView_1 = QtWidgets.QTableView(self.centralwidget)  #
        self.tableView_1.horizontalHeader().setStretchLastSection(True)  # выравнивает ширину столбцов по ширине окна
        self.sti_tv1 = QtGui.QStandardItemModel(parent=self.tableView_1)
        self.sti_tv1.setHorizontalHeaderLabels(['Parameter name', 'Measured value', 'Required value'])
        for row in range(len(tv1_lst1)):
            item1 = QtGui.QStandardItem(tv1_lst1[row])
#            item1.setFont(QFont("Consolas",20))
#            item1.setCheckable(False)
#            item1.setCheckState(QtCore.Qt.Unchecked)
            item2 = QtGui.QStandardItem(tv1_lst2[row])
            item3 = QtGui.QStandardItem(tv1_lst3[row])
            self.sti_tv1.appendRow([item1, item2, item3])

        self.tableView_1.setModel(self.sti_tv1)
        self.tableView_1.setGeometry(QtCore.QRect(2, 381, 421, 381))
        self.tableView_1.setObjectName("tableView_1")
        self.tableView_1.activated["QModelIndex"].connect(self.Tbl1_on_activated)        # ===>>>

# tableView_2
        self.tableView_2 = QtWidgets.QTableView(self.centralwidget)
        self.tableView_2.horizontalHeader().setStretchLastSection(True)  # выравнивает ширину столбцов по ширине окна
        self.sti_tv2 = QtGui.QStandardItemModel(parent=self.tableView_2)
        self.sti_tv2.setHorizontalHeaderLabels(['Parameter name', 'Measured value', 'Required value'])
        for row in range(len(tv2_lst1)):
            item1 = QtGui.QStandardItem(tv2_lst1[row])
            item1.setCheckable(False)
            item2 = QtGui.QStandardItem(tv2_lst2[row])
            item3 = QtGui.QStandardItem(tv2_lst3[row])
            self.sti_tv2.appendRow([item1, item2, item3])

        self.tableView_2.setModel(self.sti_tv2)
        self.tableView_2.setGeometry(QtCore.QRect(427, 381, 421, 381))
        self.tableView_2.setObjectName("tableView_2")
        self.tableView_2.activated["QModelIndex"].connect(self.Tbl2_on_activated)        # ===>>>

    def List1Expand(self):
        if self.checkBox_L1_exp.checkState():
            self.textEdit_1.setGeometry(QtCore.QRect(2, 22, 848, 341))
            self.textEdit_2.hide()
            self.comboBox_2.hide()
            # self.List1Update
        else:
            self.textEdit_1.setGeometry(QtCore.QRect(2, 22, 421, 341))
            self.textEdit_2.show()
            self.comboBox_2.show()
            # self.List1Update

############################################################################################
# class ADB_App_Main. Methods
    def change_iperf_port(self):
        global IPERF3_PORT
        logger.info(f'Iperf base port changed to {self.lineEdit_iperf_port.text()}')
        IPERF3_PORT = int(self.lineEdit_iperf_port.text())
        IPERF2_PORT_UDP = IPERF3_PORT + 10
        IPERF2_PORT_TCP = IPERF3_PORT + 20


    def iperf_client_break(self):
        print('break')
        self.c.breakiperf.emit()

    def break_action(self):
        print('Break signal received!')
        self.iperf_break = True

    def iperf2_version_chosen(self):
        global IPERF3_PORT, IPERF2_PORT_TCP, IPERF2_PORT_UDP, iperf_srvr_ver
        self.iperf_version = 2
        iperf_srvr_ver = 'iperf'
        self.label_18.setText("Iperf 2")
        self.label_18.setStyleSheet('background : #f0f0f0; font-weight: 500; color: darkred; font-size:10pt;')
        self.checkBox_flush.setText("Enhance")
        self.checkBox_flush.setChecked(False)
        logger.info(f'Iperf version = {self.iperf_version}, base port = {self.lineEdit_iperf_port.text()}')
        IPERF3_PORT = int(self.lineEdit_iperf_port.text())
        IPERF2_PORT_TCP = int(self.lineEdit_iperf_port.text()) + 10
        IPERF2_PORT_UDP = int(self.lineEdit_iperf_port.text())+20
        logger.debug(f'Iperf srvr_ver = {iperf_srvr_ver}, iperf2 tcp port = {IPERF2_PORT_TCP}, iperf2 udp port = {IPERF2_PORT_UDP}')

    def iperf3_version_chosen(self):
        global IPERF3_PORT, IPERF2_PORT_TCP, IPERF2_PORT_UDP, iperf_srvr_ver
        self.iperf_version = 3
        iperf_srvr_ver = 'iperf3'
        self.label_18.setText("Iperf 3")
        self.label_18.setStyleSheet('background : #f0f0f0; font-weight: 500; color: darkgreen; font-size:10pt;')
        self.checkBox_flush.setText("Flush")
        logger.info(f'Iperf version = {self.iperf_version}, base port = {self.lineEdit_iperf_port.text()}')
        IPERF3_PORT = int(self.lineEdit_iperf_port.text())
        IPERF2_PORT_TCP = int(self.lineEdit_iperf_port.text()) + 10
        IPERF2_PORT_UDP = int(self.lineEdit_iperf_port.text())+20
        logger.debug(f'Iperf srvr_ver = {iperf_srvr_ver}, iperf2 tcp port = {IPERF2_PORT_TCP}, iperf2 udp port = {IPERF2_PORT_UDP}')


    def Tbl1_on_activated(self, ind):
        global dAtt
        logger.debug(f'Tbl1_on_activated {ind.data}, row: {ind.row()}, column: {ind.column()}')
        if ind.column() == 2:
            if tv1_lst2[ind.row()] not in [None, 'N/A']:
                if (tv1_lst1[ind.row()] in ['mSS', 'RSSI', 'RSCP', 'RSRP', 'ssRsrp'] and
                   re.match("[-+]?\d+$", ind.data())):  # Signal Strength values, can be calculated
                    dAtt = int(tv1_lst2[ind.row()]) - int(ind.data()) 
                    logger.debug(f'({tv1_lst1[ind.row()]} now is  {tv1_lst2[ind.row()]} db. Should be attenuated '
                                 f'to {ind.data()} dB. Attenuation should be changed to {dAtt} dB')
                    self.statusBar().setStyleSheet("background-color : lightgreen")
                    self.statusBar().showMessage('Attenuation should be changed to ' + str(dAtt) + 'dB', 10000)
                    if not atconn:
                        self.statusBar().setStyleSheet("background-color : red")
                        self.statusBar().showMessage('Connect to Attenuator first!', 10000)
                        return
                    for attchn in att_chnl_lst:
                        attrslt = attenuator_channel_value_change_main(attipstr, attchn, dAtt)
                        if 'cannot' in attrslt:
                            self.statusBar().setStyleSheet("background-color : red")
                            self.statusBar().showMessage(attrslt, 20000)
                        elif 'successfully' in attrslt:
                            self.statusBar().setStyleSheet("background-color : lightgreen")
                            self.statusBar().showMessage(attrslt, 10000)
                            self.SignalMeasurement()
                            self.checkBox_meas.setChecked(1)
                        else:
                            self.statusBar().setStyleSheet("background-color : purple")
                            self.statusBar().showMessage(attrslt, 20000)
                        QtWidgets.qApp.processEvents()  # Cycle Renew

                elif tv1_lst1[ind.row()] in ['EcNo', 'SNR', 'SINR', 'EcNo', 'ssSinr']:  # SNR vals, cannot be calculated
                    dAtt = None
                    logger.debug(f'{tv1_lst1[ind.row()]} now is {tv1_lst2[ind.row()]} db. Should be changed to {ind.data()} db. '
                                 f'Required attenuation for SNR is not known')
                    self.statusBar().setStyleSheet("background-color : red")
                    self.statusBar().showMessage('Required attenuation for SNR is not known, '
                                                 'try changing signal LEVELS', 10000)
                elif tv1_lst1[ind.row()] in ['RSRQ', 'ssRsrq']:  # Quality values, cannot be calculated
                    dAtt = None
                    logger.debug(f'{tv1_lst1[ind.row()]} now is {tv1_lst2[ind.row()]} db. Should be changed to {ind.data()} db. '
                                 f'Required attenuation for Quality is not known')
                    self.statusBar().setStyleSheet("background-color : red")
                    self.statusBar().showMessage('Required attenuation for Quality is not known, '\
                                                 'try changing signal LEVELS', 10000)
                else:  # Other values, may be cannot be calculated
                    dAtt = None
                    logger.debug(f'{tv1_lst1[ind.row()]} now is {tv1_lst2[ind.row()]} db. Should be changed to {ind.data()} db. '
                                 f'Required attenuation is not known')
                    self.statusBar().setStyleSheet("background-color : red")
                    self.statusBar().showMessage('Required attenuation is not known, try changing signal LEVELS', 10000)
    
    def Tbl2_on_activated(self, ind):
        global dAtt
        logger.debug(f'Tbl1_on_activated {ind.data}, row: {ind.row()}, column: {ind.column()}')
        if ind.column() == 2:
            if tv2_lst2[ind.row()] not in [None, 'N/A']:
                if (tv2_lst1[ind.row()] in ['RSCP', 'RSSI', 'RSRP', 'ssRsrp'] and
                   re.match("[-+]?\d+$", ind.data())):
                    dAtt = int(tv2_lst2[ind.row()]) - int(ind.data()) 
                    logger.debug(f'({tv2_lst1[ind.row()]} now is  {tv2_lst2[ind.row()]} db. Should be attenuated '
                                 f'to {ind.data()} dB. Attenuation should be changed to {dAtt} dB')
                    self.statusBar().setStyleSheet("background-color : lightgreen")
                    self.statusBar().showMessage(f'Attenuation should be changed to {dAtt} dB', 10000)
                    if not atconn:
                        self.statusBar().setStyleSheet("background-color : red")
                        self.statusBar().showMessage('Connect to Attenuator first!', 10000)
                        return
                    for attchn in att_chnl_lst:
                        attrslt = attenuator_channel_value_change_main(attipstr, attchn, dAtt)
                        if 'cannot' in attrslt:
                            self.statusBar().setStyleSheet("background-color : red")
                            self.statusBar().showMessage(attrslt, 20000)
                        elif 'successfully' in attrslt:
                            self.statusBar().setStyleSheet("background-color : lightgreen")
                            self.statusBar().showMessage(attrslt, 10000)
                            self.SignalMeasurement
                            self.checkBox_meas.setChecked(1)
                        else:
                            self.statusBar().setStyleSheet("background-color : purple")
                            self.statusBar().showMessage(attrslt, 20000)
                        QtWidgets.qApp.processEvents()  # Cycle Renew

                elif tv2_lst1[ind.row()] in ['SNR', 'SINR', 'EcNo', 'ssSinr']:
                    dAtt = None
                    logger.debug(f'{tv2_lst1[ind.row()]} now is {tv2_lst2[ind.row()]} db. Should be changed to {ind.data()} db. '
                                 f'Required attenuation for SNR is not known')
                    self.statusBar().setStyleSheet("background-color : red")
                    self.statusBar().showMessage('Required attenuation for SNR is not known, try changing signal '
                                                 'LEVELS', 20000)
                elif tv2_lst1[ind.row()] in ['RSRQ', 'ssRsrq']:
                    dAtt = None
                    logger.debug(f'{tv2_lst1[ind.row()]} now is {tv2_lst2[ind.row()]} db. Should be changed to {ind.data()} db. '
                                 f'Required attenuation for Quality is not known')
                    self.statusBar().setStyleSheet("background-color : red")
                    self.statusBar().showMessage('Required attenuation for Quality is not known, '
                                                 'try changing signal LEVELS', 20000)
                else:
                    dAtt = None
                    logger.debug(f'{tv2_lst1[ind.row()]} now is {tv2_lst2[ind.row()]} db. Should be changed to {ind.data()} db. '
                                 f'Required attenuation is not known')
                    self.statusBar().setStyleSheet("background-color : red")
                    self.statusBar().showMessage('Required attenuation is not known, try changing signal LEVELS', 20000)

############################################################################################
# class ADB_App_Main. Methods

    def periodic_signal_measurement_main(self):
        logger.debug(f'---------------: call periodic_signal_measurement_main: {self.checkBox_meas.checkState()}')
        if not DevModel:
            self.display_message_box(2, 'Warning!', 'Please, Connect ADB first')
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
            return
        if self.checkBox_meas.checkState() == 2:
            time = 1000
            self.checkBox_meas.setText("1sec.")
            self.timer.start(time)
        elif self.checkBox_meas.checkState() == 1:
            time = 3000
            self.checkBox_meas.setText("3sec.")
            self.timer.start(time)
        else:
            self.timer.stop()
            self.checkBox_meas.setText("Continous")


    def update_func(self):
        self.SignalMeasurement()  # inside it Measonly = True

    def periodic_iperf_client_timeout(self):
        global watchdog_timer_expired
        logger.debug('---------------: call periodic_iperf_client_timeout (EXPIRED)')
        self.periodic_iperf_client_timer_stop()
        self.label_watch.setHidden(True)
        s = threading.Thread(target = kill_iperf_clients, args=(self.iperf_version,)).start()
        self.label_watch.setStyleSheet('background : #0f0f0f; font-weight: 400; color: lightblue; font-size:8pt;')
        QtWidgets.qApp.processEvents()  # Cycle Renew
        time.sleep(0.1)
        if watchdog_timer_expired:
            self.label_watch.setText('EXPIRED')
            self.label_watch.setStyleSheet('background : #f0f0f0; font-weight: 500; color: red; font-size:10pt;')
            QtWidgets.qApp.processEvents()  # Cycle Renew
        watchdog_timer_expired = False
        # time.sleep(0.2)
        # self.label_watch.setHidden(True)
        # s = self.kill_iperf_client()
        # raise subprocess.TimeoutExpired(torun, TIMEOUT_IPERF_CLIENT) # Watchdog2
        # raise IOError("watchdog2")

    def periodic_iperf_client_timer_start(self):
        if self.checkBox_sum.checkState():
            timeout_addition_for_threads = 2 # add 2 sec for threads (summary waiting)
            # timeout_addition_for_threads += int(self.lineEdit_iperf_tcp_sessions.text())//10 # add 1s per each 10 threads
        else:
            timeout_addition_for_threads = 0
            timeout_addition_for_threads = int(self.lineEdit_iperf_tcp_sessions.text())//10 # add 1s per each 10 threads
        self.iperf_current_timeout_value = TIMEOUT_IPERF_CLIENT + timeout_addition_for_threads
        time_w = int(self.iperf_current_timeout_value * 1000)
        logger.debug(f'---------------: call periodic_iperf_client_start for {time_w}msec')
        if not self.watchdog_type:
            self.timer_iperf.stop()
            self.timer_iperf.start(time_w)
        else:
            self.watchdog = Watchdog(timeout_parm=self.iperf_current_timeout_value)
        self.label_watch.setText(f'Watchdog: {self.iperf_current_timeout_value}s')
        self.label_watch.setHidden(False)
        self.label_watch.setStyleSheet('background : #f0f0f0; font-weight: 400; color: darkred; font-size:8pt;')

    def periodic_iperf_client_timer_restart(self):
        if self.checkBox_sum.checkState():
            timeout_addition_for_threads = 2  # add 2 sec for threads (summary waiting)
            # timeout_addition_for_threads += int(self.lineEdit_iperf_tcp_sessions.text())//10 # add 1s per each 10 threads
        else:  # WATCHDOG type
            timeout_addition_for_threads = 0
            # timeout_addition_for_threads = int(self.lineEdit_iperf_tcp_sessions.text())//10 # add 1s per each 10 threads
        self.iperf_current_timeout_value = TIMEOUT_IPERF_CLIENT + timeout_addition_for_threads
        time_w = int(self.iperf_current_timeout_value * 1000)
        self.label_watch.setStyleSheet('background : #0f0f0f; font-weight: 400; color: lightblue; font-size:8pt;')
        QtWidgets.qApp.processEvents()  # Cycle Renew
        time.sleep(0.1)
        logger.debug(f'---------------: call periodic_iperf_client_restart for {time_w}msec')
        if not self.watchdog_type:
            self.timer_iperf.stop()
            self.timer_iperf.start(time_w)
        else:  # WATCHDOG type
            self.watchdog.reset()
        self.label_watch.setText(f'Watchdog: {self.iperf_current_timeout_value}s')
        self.label_watch.setHidden(False)
        self.label_watch.setStyleSheet('background : #f0f0f0; font-weight: 400; color: darkred; font-size:8pt;')
        QtWidgets.qApp.processEvents()  # Cycle Renew

    def periodic_iperf_client_timer_stop(self):
        global watchdog_timer_expired
        logger.debug('---------------: call periodic_iperf_client_timer_stop')
        if not self.watchdog_type:
            self.timer_iperf.stop()
        else:
            self.watchdog.stop()
        self.label_watch.setStyleSheet('background : #0f0f0f; font-weight: 400; color: lightblue; font-size:8pt;')
        QtWidgets.qApp.processEvents()  # Cycle Renew
        time.sleep(0.1)
        self.label_watch.setStyleSheet('background : #f0f0f0; font-weight: 500; color: red; font-size:8pt;')
        QtWidgets.qApp.processEvents()  # Cycle Renew
        time.sleep(0.1)
        self.label_watch.setHidden(True)
        if watchdog_timer_expired:
            logger.info(f'watchdog_timer_expired:{watchdog_timer_expired}')
            self.label_watch.setText('Expired')
            self.label_watch.setHidden(False)
            self.label_watch.setStyleSheet('background : #0f0f0f; font-weight: 500; color: red; font-size:10pt;')
            QtWidgets.qApp.processEvents()  # Cycle Renew
            time.sleep(2)
            watchdog_timer_expired = False



    def kill_iperf_client(self):
        ''' Derive process id of the runned iperf/ipef3 at Android device and kill it'''
        iperf_v = iperf2_version if self.iperf_version == 2 else iperf3_version
        logger.info(f'---------------: called kill_iperf_client iperf version:{iperf_v}' )
        s = torun + 'shell pidof '+ iperf_v
        p = (subprocess.run(s, capture_output=True, text=True, shell=True))
        if p.returncode > 0:
            logger.debug('---------------: Error: ' + p.stderr)
            logger.debug('---------------: Output: ' + p.stdout)
            logging.debug("pidof doesn't work")
            return "pidof doesn't work"
        else:
            pid = p.stdout.replace('\n','')
            pids = re.findall(r'\d+',pid)
            logger.debug(f'PIDs found:{pids}')
            killresult = True
            if len(pids)>0:
                for pid in pids:
                    logger.debug(f'processing PID:{pid}')
                    s = f'{torun} shell "kill -s 1 {pid}"' # send to pid sig#1 Hangup(HUP)
                    p = (subprocess.run(s, capture_output=True, text=True, shell=True))
                    print(f'>{s}')
                    if p.returncode > 0:
                        logger.debug('---------------: Error: ' + p.stderr)
                        logger.debug('---------------: Output: ' + p.stdout)
                        killresult = False
                        logging.debug(f'kill PID:{pid} NOK, returncode:{p.returncode}, out = {p.stdout}')
                    else:
                        logging.debug(f'PID:{pid} successfully killed:{p.stdout}')
                        killresult = killresult and True
            if killresult:
                return 'killed'
            else:
                return f'cannot kill OR bad PID:{pid} or process already finished'

    # Lst_l1 append (10)
    def append_records_lst_l1(self):
        logger.debug('---------------: call append_records_lst_l1')
        self.textEdit_1.setTextBackgroundColor(self.whiteColor)
        self.textEdit_1.setFontPointSize(10)
        for row in range(len(lst_l1)):
            if ('OUT_OF_SERVICE' in lst_l1[row]
                or 'POWER_OFF' in lst_l1[row]):
                self.textEdit_1.append(colored_text(lst_l1[row], col_val='#700000', weight=600))
            elif 'IN_SERVICE' in lst_l1[row]:
                self.textEdit_1.append(colored_text(lst_l1[row], col_val='#007000', weight=600))
            else:
                self.textEdit_1.append(colored_text(lst_l1[row], col_val='#000000', weight=450))

        self.textEdit_1.verticalScrollBar().setValue(0) # OK


# Lst_l2 append (10)
    def append_records_lst_l2(self):
        logger.debug('---------------: call append_records_lst_l2')
        self.textEdit_1.setTextBackgroundColor(self.whiteColor)
        self.textEdit_2.setFontPointSize(10)

        for row in range(len(lst_l2)):
            if ('OUT_OF_SERVICE' in lst_l2[row]
            or 'POWER_OFF' in lst_l2[row]):
                self.textEdit_2.append(colored_text(lst_l2[row], col_val='#700000', weight=600))
            elif 'IN_SERVICE' in lst_l2[row]:
                self.textEdit_2.append(colored_text(lst_l2[row], col_val='#007000', weight=600))
            else:
                self.textEdit_2.append(colored_text(lst_l2[row], col_val='#000000', weight=450))
        self.textEdit_2.verticalScrollBar().setValue(0) #OK

# Disk info (9)
    def append_recs_disk_info_l1(self):
        logger.debug('---------------: call appendRecs8')
        self.textEdit_1.setFontPointSize(9)
        if len(procdata) >= 8:
            for row in range(len(procdata[8])):
                if 'storage/emulated' in procdata[8][row]:
                    self.textEdit_1.setTextBackgroundColor(self.lightgreenColor)
                else:
                    self.textEdit_1.setTextBackgroundColor(self.whiteColor)
                self.textEdit_1.append(procdata[8][row])
        else:
            logger.warning('---------------: No data available')
            self.textEdit_1.append('No data available')

    def append_recs_disk_info_l2(self):
        logger.debug('---------------: call appendRecs8_l2')
        self.textEdit_2.setFontPointSize(9)
        if len(procdata) >= 8:
            for row in range(len(procdata[8])):
                if 'storage/emulated' in procdata[8][row]:
                    self.textEdit_2.setTextBackgroundColor(self.lightgreenColor)
                else:
                    self.textEdit_2.setTextBackgroundColor(self.whiteColor)
                self.textEdit_2.append(procdata[8][row])
        else:
            logger.warning('---------------: No data available')
            self.textEdit_2.append('No data available')

    ############################################################################################
    # class ADB_App_Main. Methods

    # IP interfaces (8)
    def append_recs_ip_info_l1(self):
        logger.debug('---------------: call appendRecs6')
        self.textEdit_1.setTextBackgroundColor(self.whiteColor)
#        if self.textEdit_1.fontPointSize() > 8:
        self.textEdit_1.setFontPointSize(8)
        if len(procdata) >= 6:
            for row in range(len(procdata[6])):
                if (mif
                    and mif in procdata[6][row]):       # if mif != '' != None
                    self.textEdit_1.setTextBackgroundColor(self.yellowColor)
                elif wif in procdata[6][row]:
                    self.textEdit_1.setTextBackgroundColor(self.lightgreenColor)
                else:
                    self.textEdit_1.setTextBackgroundColor(self.whiteColor)
                self.textEdit_1.append(procdata[6][row])
        else:
            logger.warning('---------------: No data available')
            self.textEdit_1.append('No data available')

    def append_recs_ip_info_l2(self):
        logger.debug('---------------: call appendRecs6_l2')
        self.textEdit_2.setTextBackgroundColor(self.whiteColor)
        self.textEdit_2.setFontPointSize(8)
        if len(procdata) >= 6:
            for row in range(len(procdata[6])):
                if (mif
                    and mif in procdata[6][row]):       # if mif != '' != None
                    self.textEdit_2.setTextBackgroundColor(self.yellowColor)
                elif wif in procdata[6][row]:
                    self.textEdit_2.setTextBackgroundColor(self.lightgreenColor)
                else:
                    self.textEdit_2.setTextBackgroundColor(self.whiteColor)
                self.textEdit_2.append(procdata[6][row])
            self.textEdit_2.verticalScrollBar().setValue(0) # OK
            # self.textEdit_2.verticalScrollBar().setValue(self.textEdit_2.verticalScrollBar().maximum()) # OK
        else:
            logger.warning('---------------: No data available')
            self.textEdit_2.append('No data available')

    # Battery info ==> # Disk info
    #    def appendRecs8(self):
    #        if len(procdata)>=8:
    #            for row in range(len(procdata[8])):
    #                self.textEdit_1.append(procdata[8][row])

    # WiFi Scanner (3)
    def append_recs_wifi_scan_data_l1(self):
        logger.debug('---------------: call appendRecsWiFiScanData')
        if DevModel:
            if self.checkBox_L1_exp.checkState():
                self.textEdit_1.setFontPointSize(8)
            else:
                self.textEdit_1.setFontPointSize(3.3)
            self.textEdit_1.append(WiFiScanData)
        else:
            self.textEdit_1.setFontPointSize(10)
            self.textEdit_1.append('ADB is not connected')

    def append_recs_wifi_scan_data_l2(self):
        logger.debug('---------------: call appendRecsWiFiScanData_l2')
        if DevModel:
            self.textEdit_2.setFontPointSize(3.3)
            self.textEdit_2.append(WiFiScanData)
        else:
            self.textEdit_2.setFontPointSize(10)
            self.textEdit_2.append('ADB is not connected')

# PKG installation results()
    def append_recs_pkg_installation_l1(self):
        logger.debug('---------------: call appendRecsPKGinst')
        self.textEdit_1.setFontPointSize(8)
        logger.info(f'ls:  {pkglst}, len: {len(pkglst)}')
        # for i in range(len(pkglst)):
        self.textEdit_1.append(pkglst)

    def append_recs_pkg_installation_l2(self):
        logger.debug('---------------: call appendRecsPKGinst_l2')
        self.textEdit_2.setFontPointSize(8)
        logger.info(f'Results: {self.pkginst} , len: {len(self.pkginst)}')  # self.widget.res
        for i in range(len(self.pkginst)):  # self.widget.res[]
            self.textEdit_2.append(self.pkginst[i])
            logger.info('Results: ' + str(i) + ' : ' + self.pkginst[i])

# APK installation results()
    def append_recs_apk_installation_l1(self):
        logger.debug('---------------: call appendRecsAPKinst')
        if self.checkBox_L1_exp.checkState():
            self.textEdit_1.setFontPointSize(10)
        else:
            self.textEdit_1.setFontPointSize(8)
        logger.debug('apk list records: ' + str(len(apklst)))
        logger.debug('installed apk list: ' + str(apklst))
        self.textEdit_1.append(apklst)
        self.textEdit_1.verticalScrollBar().setValue(0)

    def append_recs_apk_installation_l2(self):
        logger.debug('---------------: call appendRecsAPKinst_l2')
        self.textEdit_2.setFontPointSize(8)
        logger.debug('Results: ' + str(len(self.apkinst)))
        logger.debug('Installed APKs: ' + str(self.apkinst))  # self.widget.res
        for i in range(len(self.apkinst)):  # self.widget.res
            self.textEdit_2.append(self.apkinst[i])
            logger.info('---------------: Apkinst: ' + str(i) + ' : ' + self.apkinst[i])
            logger.info(f'Results: {i}, {self.apkinst[i]}')  # self.widget.res

# WiFi info (12)
    def append_recs_wifi_info_l1(self):
        logger.debug('---------------: call appendRecsWiFiInfo')
        if len(procdata) >= 8:
            p7 = []
            p7.extend(re.split(",",procdata[7][0]))
            for row in range(len(p7)):
                self.textEdit_1.setFontPointSize(12)
                self.textEdit_1.append(p7[row])
        else:
            logger.warning('---------------: No data available')
            self.textEdit_1.setFontPointSize(14)
            self.textEdit_1.append('No data available')


    def append_recs_wifi_info_l2(self):
        logger.debug('---------------: call appendRecsWiFiInfo_l2')
        if len(procdata) >= 8:
            p7 = []
            p7.extend(re.split(",", procdata[7][0]))
            for row in range(len(p7)):
                self.textEdit_2.setFontPointSize(12)
                self.textEdit_2.append(p7[row])
        else:
            logger.warning('---------------: No data available')
            self.textEdit_1.setFontPointSize(14)
            self.textEdit_1.append('No data available')

    # Battery info (10)
    def append_recs_bat_info_l1(self):
        logger.debug('---------------: call append_recs_bat_info_l1')
        if len(procdata) >= 9:
            # p9 = []
            # p9.extend(re.split(",",procdata[9]))
            for row in range(len(procdata[9])):
                self.textEdit_1.setFontPointSize(12)
                self.textEdit_1.append(procdata[9][row])
        else:
            logger.warning('---------------: No data available')
            self.textEdit_1.setFontPointSize(14)
            self.textEdit_1.append('No data available')

    def append_recs_bat_info_l2(self):
        logger.debug('---------------: call append_recs_bat_info_l2')
        if len(procdata) >= 9:
            # p9 = []
            # p9.extend(re.split(",",procdata[9]))
            for row in range(len(procdata[9])):
                self.textEdit_2.setFontPointSize(12)
                self.textEdit_2.append(procdata[9][row])
        else:
            logger.warning('---------------: No data available')
            self.textEdit_2.setFontPointSize(14)
            self.textEdit_2.append('No data available')

# iperf (6)
    def append_recs_iperf_client_l1(self):  # iperf client
        logger.debug('---------------: call appendRecsIperfClnt')
        if self.checkBox_L1_exp.checkState():
            self.textEdit_1.setFontPointSize(10)
        else:
            self.textEdit_1.setFontPointSize(7)
        for s in self.iperf_clnt_lst:
            self.textEdit_1.append(str(s)) 

    def append_recs_iperf_server_l2(self):  # iperf server
        logger.debug('---------------: call appendRecsIperfSrv')
        self.textEdit_2.setFontPointSize(8)
        for s in self.iperf_srvr_log_lst:
            self.textEdit_2.append(str(s))  # could be filtered there if required ################

##########################################
# display tv_lst1
    def appendRecs_tv1(self):
        for i in range(min(len(tv1_lst1), len(tv1_lst2), len(tv1_lst1))):
            item1 = QtGui.QStandardItem(tv1_lst1[i])
            item1.setFont(QFont("Tahoma",10, weight=450 ))
            item1.setCheckable(False)
#            item_1.setCheckState(QtCore.Qt.Unchecked)
            item2 = QtGui.QStandardItem(str(tv1_lst2[i]))
            item3 = QtGui.QStandardItem(tv1_lst3[i])
            self.sti_tv1.appendRow([item1, item2, item3])
        for row in range(len(tv1_lst1)):
            self.tableView_1.setRowHeight(row, 25)
        self.tableView_1.setColumnWidth(0, 120)
        self.tableView_1.setColumnWidth(1, 180)
        self.tableView_1.setColumnWidth(2, 20)

    ############################################################################################
    # class ADB_App_Main. Methods

    ##########################################
    # display tv_lst2
    def appendRecs_tv2(self):
        for i in range(min(len(tv2_lst1), len(tv2_lst2), len(tv2_lst1))):
            item1 = QtGui.QStandardItem(tv2_lst1[i])
            item1.setFont(QFont("Tahoma",10, weight=450 ))
            item1.setCheckable(False)
#            item_1.setCheckState(QtCore.Qt.Unchecked)
            item2 = QtGui.QStandardItem(str(tv2_lst2[i]))
            item3 = QtGui.QStandardItem(tv2_lst3[i])
            self.sti_tv2.appendRow([item1, item2, item3])
        for row in range(len(tv2_lst1)):
            self.tableView_2.setRowHeight(row, 25)
        self.tableView_2.setColumnWidth(0, 120)
        self.tableView_2.setColumnWidth(1, 180)
        self.tableView_2.setColumnWidth(2, 20)

################################
# remove All TableView  rows tvxx
    def removeRecs_tv1(self):
        logger.debug('---------------: call removeRecs_tv1')
        self.sti_tv1.removeRows(0, self.sti_tv1.rowCount())

    def removeRecs_tv2(self):
        logger.debug('---------------: call removeRecs_tv1')
        self.sti_tv2.removeRows(0, self.sti_tv2.rowCount())

############################################################################################
# class ADB_App_Main. Methods

# RAM info (7/10)
    def appendRecs1013(self):
        logger.debug('---------------: call appendRecs1013')
        if self.checkBox_L1_exp.checkState():
            self.textEdit_1.setFontPointSize(10)
        else:
            self.textEdit_1.setFontPointSize(7)
        if len(procdata) >= 11:
            for row in range(len(procdata[10])):
                self.textEdit_1.append(procdata[10][row])
            self.textEdit_1.setFontPointSize(10)
            for row in range(len(procdata[11])):
                if 'MemTotal' in procdata[11][row]:
                    self.textEdit_1.setTextBackgroundColor(self.lightgreenColor)
                else:
                    self.textEdit_1.setTextBackgroundColor(self.whiteColor)
                self.textEdit_1.append(procdata[11][row])
#            for row in range(len(procdata[12])):
#                self.textEdit_1.append(procdata[12][row])
#            for row in range(len(procdata[13])):
#                self.textEdit_1.append(procdata[13][row])
            self.textEdit_1.verticalScrollBar().setValue(0)
        else:
            logger.warning('---------------: No data available')
            self.textEdit_1.setFontPointSize(10)
            self.textEdit_1.append('No data available')

    def appendRecs1013_l2(self):
        logger.debug('---------------: call appendRecs1013')
        if self.checkBox_L1_exp.checkState():
            self.textEdit_2.setFontPointSize(10)
        else:
            self.textEdit_2.setFontPointSize(7)
        if len(procdata) >= 11:
            for row in range(len(procdata[10])):
                self.textEdit_2.append(procdata[10][row])
            self.textEdit_2.setFontPointSize(10)
            for row in range(len(procdata[11])):
                if 'MemTotal' in procdata[11][row]:
                    self.textEdit_2.setTextBackgroundColor(self.lightgreenColor)
                else:
                    self.textEdit_2.setTextBackgroundColor(self.whiteColor)
                self.textEdit_2.append(procdata[11][row])
#            for row in range(len(procdata[12])):
#                self.textEdit_2.append(procdata[12][row])
#            for row in range(len(procdata[13])):
#                self.textEdit_2.append(procdata[13][row])
            self.textEdit_1.verticalScrollBar().setValue(0)
        else:
            logger.warning('---------------: No data available')
            self.textEdit_2.setFontPointSize(10)
            self.textEdit_2.append('No data available')

# Clear all text records
    def clearRecs_l1(self):
        logger.debug('---------------: call clearRecs_l1')
        self.textEdit_1.clear()

    def clearRecs_l2(self):
        logger.debug('---------------: call clearRecs_l2')
        self.textEdit_2.clear()

############################################################################################
# class ADB_App_Main. Methods

    def kill_iperfs_set(self):
        logger.debug('---------------: kill_iperfs_set')
        self.comboBox_1.setCurrentIndex(self.common_index)  # switch comboboxes to Common at first
        self.comboBox_2.setCurrentIndex(self.common_index)
        p = get_iperf_instances_from_server(iperf_srvr_cmd2chk)  # prepare list of iperf instances
        self.iperf_srvr_log_lst.extend(p)
        self.iperfwidget = CreateIperfsListToKill()
        if self.iperfwidget.exec_():
            self.iperfinst = self.iperfwidget.res
            self.iperf_srvr_log_lst.extend(self.iperfwidget.p)
            if len(self.iperfinst) > 0:
                for one in self.iperfinst:
                    self.statusBar().setStyleSheet("background-color : green")
                    self.statusBar().showMessage(one, 10000)
                logger.debug('iperf instances kill results: ' + str(self.iperfwidget.res))
            self.comboBox_1.setCurrentIndex(self.iperf_index)
            self.comboBox_2.setCurrentIndex(self.iperf_index)

    def run_iperfs_set(self):
        logger.debug('---------------: run_iperfs_set')
        self.comboBox_1.setCurrentIndex(self.common_index)  # switch comboboxes to Common at first
        self.comboBox_2.setCurrentIndex(self.common_index)
        self.isrvr2run_widget = CreateIperfsListToRun()
        if self.isrvr2run_widget.exec_():
            self.iperfsrvrs2run = self.isrvr2run_widget.res
            self.iperf_srvr_log_lst.extend(self.isrvr2run_widget.p)
            if len(self.iperfsrvrs2run) > 0:
                for one in self.iperfsrvrs2run:
                    if self.isrvr2run_widget.to_rerun:
                        self.display_message_box(2,"Warning", "Before run new iperf daemon instace, please, reconnect and kill existing one!")
                        return
                    self.statusBar().setStyleSheet("background-color : green")
                    self.statusBar().showMessage(one, 10000)
                logger.debug('iperf 2 run selection results: ' + str(self.isrvr2run_widget.res))
            self.comboBox_1.setCurrentIndex(self.iperf_index)
            self.comboBox_2.setCurrentIndex(self.iperf_index)

    def Get_iperfs_list_from_server(self, sshipstr, sshport, sshname, sshpwd):
        """
        Inflate list of installed iperf versions on the server using ps -eaf command
        Return: global Liperfsrvrs
        """
    # L_iperfsrvrs2run = [] # selected iperf executables to run as daemon servers
        global Liperfsrvrs  # founded iperf executables at the SSH server to select which should be runned
        Liperfsrvrs = []
        self.L_iperfsrvrs = []  # clear list of found iperfs in PATH
        logger.debug('---------------: call Get_iperfs_list_from_server()')    
        [p, e] = exec_linux_command('whereis iperf')  # ------------------------------> run via SSH cmd 'whereis iperf'
        logger.debug('---------------: Output(2): ')    
        if len(e) == 0:
            for s in p:
                ss = s.split(" ")
                for sss in ss:
                    logger.debug('---------------:', sss)
                    if ('.gz' not in sss and
                       '.deb' not in sss and
                       'man' not in sss and
                       sss != ''):
                        l = sss.replace(':', '').replace('\n', '')
                        self.L_iperfsrvrs.append(l)
                        Liperfsrvrs.append(l)
            for s in self.L_iperfsrvrs:
                logger.debug('---------------: ' + s)
        else:
            logger.debug('---------------: Err(2): ')    
            for s in e:
                ss = s.split(" ")
                for sss in ss:
                    logger.debug('---------------: ' + sss)
        [p, e] = exec_linux_command('whereis iperf3')  # ------------------------------> run via SSH cmd 'whereis iperf'
        logger.debug('---------------: Output(3): ')    
        if len(e) == 0:
            for s in p:
                ss = s.split(" ")
                for sss in ss:
                    logger.debug('---------------:', sss)
                    if ('.gz' not in sss and
                        '.deb' not in sss and
                        'man' not in sss and
                       sss != ''):
                        l = sss.replace(':', '').replace('\n', '')
                        self.L_iperfsrvrs.append(l)
                        Liperfsrvrs.append(l)
            for s in self.L_iperfsrvrs:
                logger.debug('---------------: ' + s)
        else:
            logger.debug('---------------: Err(3): ')    
            for s in e:
                ss = s.split(" ")
                for sss in ss:
                    logger.debug('---------------: ' + sss)

    def Install_pkg_set(self):
        """ To choose and install iperf packages set from disk to the DUT
        :param self:
        :return: self.pkginst from self.PKGwidget.res
        """
        logger.debug('---------------: call Install_pkg_set')
        if DevModel:
            self.comboBox_1.setCurrentIndex(self.common_index)  # switch comboboxes to Common at first
            self.comboBox_2.setCurrentIndex(self.common_index)
            prepare_packages_list_main()
            self.PKGwidget = CreateListPkg2Install()
            if self.PKGwidget.exec_():
                self.pkginst = self.PKGwidget.res
                if len(self.pkginst) > 0:
                    for one in self.pkginst:
                        if 'successfully' in one:
                            self.statusBar().setStyleSheet("background-color : green")
                            self.statusBar().showMessage(one, 10000)
                        else:
                            self.statusBar().setStyleSheet("background-color : red") 
                            self.statusBar().showMessage(one, 10000)
                    logger.debug('PKG Installation results: ' + str(self.PKGwidget.res))
                self.comboBox_1.setCurrentIndex(self.pkg_index)
                self.comboBox_2.setCurrentIndex(self.pkg_index)
        else:
            self.statusBar().setStyleSheet("background-color : red") 
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
            logger.debug('Please, connect device to ADB script!')
            QtWidgets.qApp.processEvents()  # Cycle Renew

    def Install_apk_set(self):
        logger.debug('---------------: call Install_apk_set')
        if DevModel:
            self.comboBox_1.setCurrentIndex(self.common_index)  # switch comboboxes to Common at first
            self.comboBox_2.setCurrentIndex(self.common_index)
            prepare_apk_list_main()
            self.APKwidget = CreateAPKsList2Install()
            if self.APKwidget.exec_():
                self.apkinst = self.APKwidget.res  # список  apk, выбранных для установки
                if len(self.apkinst) > 0:
                    for one in self.apkinst:
                        if 'Success' in one:
                            self.statusBar().setStyleSheet("background-color : green")
                            self.statusBar().showMessage(one, 10000)
                        else:
                            self.statusBar().setStyleSheet("background-color : red") 
                            self.statusBar().showMessage(one, 10000)
                    logger.debug('APK Installation results: ' + str(self.APKwidget.res))
                self.comboBox_1.setCurrentIndex(self.apk_index)
                self.comboBox_2.setCurrentIndex(self.apk_index)
        else:
            self.statusBar().setStyleSheet("background-color : red") 
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
            QtWidgets.qApp.processEvents()  # Cycle Renew
            logger.debug('Please, connect device to ADB script!')

    def ADB_device_connect(self):
        logger.debug('---------------: call ADB_device_connect')
        global Measonly
        Measonly = False  # this code NOT running  in the measurements only mode
        adb_data_reinit_main()  # for FULL data clearing
        self.progressBar_ADB.reset()

        #########################
        # Check for ADB connection
        #########################
        p = (subprocess.run(torun + 'devices', capture_output=True, text=True, shell=True))
        if not '\tdevice' in p.stdout:
            logger.error('Please, connect device with ADB debugging allowed in Developers settings ')
            # Message Box "connect device with ADB debugging allowed"
            txt = "Please, connect device with ADB debugging allowed in Developers settings"
            self.display_message_box(QtWidgets.QMessageBox.Critical, 'Alert', txt)
            return
        else:
            pp = (re.split("\r|\n", p.stdout))
            logger.info(str(pp[1]))

# Try getting Android version (debugging bridge rights checking)
        s = torun + 'shell getprop ro.build.version.release'
        p = (subprocess.run(s, capture_output=True, text=True, shell=True))
        if 'error: device unauthorized' in p.stderr:
            logger.debug(p.stderr)
            logger.error(
                'Please, authorize ADB debugging on the device (check ADB debugging allowed from this host)')
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, authorize ADB debugging on the device (check ADB debugging allowed '
                                         'from this host)', 30000)

    # Message Box "authorize ADB debugging"
            txt = "Please, authorize ADB debugging on the device (check ADB debugging allowed from this host)"
            self.display_message_box(QtWidgets.QMessageBox.Warning, 'Warning!', txt)
            return

            # Measonly = False
        self.progressBar_ADB.setValue(10)  # ====================================================================> 10%
        self.statusBar().showMessage('Waiting... Connecting to the devices via Adobe Debug Bridge.', 20000)

        get_data_from_adb_device_connect_main_01()
        self.progressBar_ADB.setValue(20)  # ====================================================================> 20%
        get_signal_measurement_data_from_adb()  # signaling
        self.progressBar_ADB.setValue(30)  # ====================================================================> 30%
        self.progressBar_ADB.setValue(40)  # ====================================================================> 40%
        get_ip_data_from_adb_device_main()
        self.progressBar_ADB.setValue(50)  # ====================================================================> 50%
        get_iphonesubinfo_main()
        self.progressBar_ADB.setValue(60)  # ====================================================================> 60%
        get_data_from_adb_device_main_03()
        self.progressBar_ADB.setValue(70)  # ====================================================================> 70%
        get_data_from_adb_device_connect_main_04()
        self.progressBar_ADB.setValue(80)  # ====================================================================> 80%
        proceed_adb_device_data()  # calculating
        self.progressBar_ADB.setValue(90)  # ====================================================================> 90%
        ADB_signal_output()  # signaling
        ADB_device_output()  # connection
        self.progressBar_ADB.setValue(100)  # ====================================================================>100%
        self.statusBar().setStyleSheet("background-color : lightgreen")
        self.statusBar().showMessage(DevName1 + ' successfully connected via Adobe Debug Bridge.')
        self.comboBox_1.setCurrentIndex(self.common_index)

        if RMq == 1:
            self.checkBox_L1_exp.setChecked(True)
        else:
            self.checkBox_L1_exp.setChecked(False)
        ###################################
        # clear ALL and display data
        self.clearRecs_l1()
        self.append_records_lst_l1()
        self.clearRecs_l2()
        self.append_records_lst_l2()
        self.removeRecs_tv1()
        self.appendRecs_tv1()
        self.removeRecs_tv2()
        self.appendRecs_tv2()

    def display_message_box(self, icon, title: str, message_text: str):
        """ Display QMessage box with  user text
        :param message_text:str
                title:  str
                icon:QtWidgets.QMessageBox
        :return: window with message
        """
        msg = QtWidgets.QMessageBox(self)
        msg.setWindowTitle(title)
        msg.setText(message_text)
        msg.setIcon(icon)
        msg.show()

    def ask_message_box(self,title: str, message_text: str):
        ''' ASk Yes| No
        :param title:str window title
        :param message_text:str message text
        :return: boolean
        '''
        msg = QtWidgets.QMessageBox(self)
        msg.setWindowTitle(title)
        msg.setText(message_text)
        msg.setStandardButtons(QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No)
        msg.setIcon(QtWidgets.QMessageBox.Question)
        button = msg.exec()

        if button == QtWidgets.QMessageBox.Yes:
            print("Yes!")
            return True
        else:
            print("No!")
            return False


    def SignalMeasurement(self):
        global Measonly
        logger.debug('---------------: call SignalMeasurement')
        if not DevModel:
            self.display_message_box(2, 'Warning!', 'Please, Connect ADB first')
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
            return
        Measonly = True
        adb_data_signal_measurements_reinit_main()  # for measurement data clearing
        self.progressBar_ADB.reset()

        # Check for ADB connection
        p = (subprocess.run(torun + 'devices -l', capture_output=True, text=True, shell=True))
        pp = (re.split("\r|\n", p.stdout))
        if pp[1] == '':
            logger.error('Please, connect device with ADB debugging allowed in Developers settings')
        self.progressBar_ADB.setValue(10)  # ====================================================================> 10%
        self.statusBar().showMessage('Waiting... Signal Measurement...', 20000)
        self.progressBar_ADB.setValue(20)  # ====================================================================> 20%
        get_signal_measurement_data_from_adb()  # signaling
        self.progressBar_ADB.setValue(50)  # =====================================================================> 50%
        proceed_adb_device_data()  # calculating
        self.progressBar_ADB.setValue(80)  # =====================================================================> 80%
        ADB_signal_output()  # signaling
        # ADB_device_output()  # connection
        self.progressBar_ADB.setValue(100)  # ====================================================================>100%
        self.statusBar().setStyleSheet("background-color : lightgreen")
        self.statusBar().showMessage(DevName1 + ' successfully measured')

        ###################################
        # clear and display ALL measurements data
        self.removeRecs_tv1()
        self.appendRecs_tv1()
        self.removeRecs_tv2()
        self.appendRecs_tv2()

    def FillMemory(self):
        logger.debug('---------------: call FillMemory')
        Sure = self.ask_message_box('Danger operation!','Device can be destroyed! Are you shure?')
        if Sure:
            if DevModel:
                fill_device_memory_main()
                self.statusBar().setStyleSheet("background-color : pink")
                self.statusBar().showMessage('Memory fill started', 10000)

                self.display_message_box(QtWidgets.QMessageBox.Information, 'Information', "Memory fill started!")
            else:
                self.statusBar().setStyleSheet("background-color : red")
                self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
                QtWidgets.qApp.processEvents()  # Cycle Renew
        else:
            return

    def ClearMemory(self):
        logger.debug('---------------: call ClearMemory')
        s = threading.Thread(target = kill_iperf_clients, args=(self.iperf_version,)).start()
        # s = self.kill_iperf_client()
        if DevModel:
            clear_device_memory_main()
            self.statusBar().setStyleSheet("background-color : lightgreen")
            self.statusBar().showMessage('Memory cleared', 10000)
            self.display_message_box(QtWidgets.QMessageBox.Information, 'Information', "Memory cleared!")
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
            QtWidgets.qApp.processEvents()  # Cycle Renew

    def WiFiOn(self):
        logger.debug('---------------: call WiFiOn')
        if DevModel:
            switch_wifi_on_main()
            self.statusBar().setStyleSheet("background-color : lightblue")
            self.statusBar().showMessage('WiFi switched ON', 10000)
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
        QtWidgets.qApp.processEvents()  # Cycle Renew

    def WiFiOff(self):
        logger.debug('---------------: call WiFiOff')
        if DevModel:
            switch_wifi_off_main()
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('WiFi switched OFF', 10000)
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
        QtWidgets.qApp.processEvents()  # Cycle Renew

    def MobDataOn(self):
        logger.debug('---------------: call MobDataOn')
        if DevModel:
            switch_mobile_data_on_main()
            self.statusBar().setStyleSheet("background-color : lightgreen")
            self.statusBar().showMessage('Mobile Data connection switched ON', 10000)
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
        QtWidgets.qApp.processEvents()  # Cycle Renew

    def MobDataOff(self):
        logger.debug('---------------: call MobDataOff')
        if DevModel:
            switch_mobile_data_off_main()
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Mobile Data connection switched OFF', 10000)
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
        QtWidgets.qApp.processEvents()  # Cycle Renew

    def DisplaySettings(self):
        logger.debug('---------------: call DisplaySettings')
        if DevModel:
            display_settings_main()
            self.statusBar().setStyleSheet("background-color : yellow")
            self.statusBar().showMessage('See Settings page at mobile device', 10000)
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('Please, connect device to ADB first!', 10000)
        QtWidgets.qApp.processEvents()  # Cycle Renew

    def Atts_clear(self):
        global atconn
        logger.debug('---------------: call Atts_clear')
        Sure = self.ask_message_box('Attention!','All entered Att. channels will be cleared to 0 dB! Are you shure?')
        if not Sure:
            return
        if not atconn:
            display_critical_message(3,'Attenuators value reset error','Connect to attenuator first!')
            return
        attipstr = self.lineEdit_Att_IP.text()
        if (len(att_chnl_lst) != 0 and          # Channel list is not free AND
           check_self_ping_to(attipstr)):  # Attenuator IP is reachable using ping cmd
            self.progressBar_Att.reset()
            self.progressBar_Att.setValue(10)  # ==================================================> 10%
            connect_attenuator_main(attipstr)
            atconn = check_attenuator_connect(attipstr, tprt)
            if atconn:
                self.progressBar_Att.setValue(50)  # ===================================================> 50%
            for attchn in att_chnl_lst:
                cA = set_attenuator_channel_str_value_with_check(attipstr, int(attchn), 0)
                if cA:
                    if (int(cA) >= 0 and
                       int(cA) < 64):
                        self.progressBar_Att.setValue(100)  # ==================================================> 100%
                    logger.info(
                        '---------------: Attenuator ' + attipstr + ' Reset Ch.' + attchn + ', att.value = ' + cA + ' dB')
                    self.statusBar().setStyleSheet("background-color : lightgreen")
                    self.statusBar().showMessage('Attenuator ' + attipstr + ' Reset Ch.'
                                                 + attchn + ', att.value = ' + cA, 20000)
                    QtWidgets.qApp.processEvents()  # Cycle Renew
            return
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('No Att. channels', 20000)
            # Message Box "Attenuator's IP unreachable"
            self.display_message_box(QtWidgets.QMessageBox.Warning, 'Warning!', "Attenuator's IP unreachable")
            QtWidgets.qApp.processEvents()  # Cycle Renew
            return


    def AttenuatorConnect(self):
        global attipstr, attchn, atconn
        logger.debug('---------------: call AttenuatorConnect')
        attipstr = self.lineEdit_Att_IP.text()
        tip = attipstr
        attinput = self.lineEdit_Att_Chn.text()

        global att_chnl_lst
        att_chnl_lst = get_att_chnl_lst_from_input(attinput)  # read attenuator channels list

        if not att_chnl_lst:
            logger.error('---------------: Wrong input in Att.Channel, exit')    

            # Message Box 'Wrong input in Att.Channel'
            self.display_message_box(QtWidgets.QMessageBox.Information, 'Warming!', "Wrong input in Att.channel!")
            return

        if (len(att_chnl_lst) != 0 and          # Channel list is not free AND
           check_self_ping_to(attipstr)):  # Attenuator IP is reachable using ping cmd
            self.progressBar_Att.reset()
            self.progressBar_Att.setValue(10)  # ==================================================> 10%
            connect_attenuator_main(attipstr)
            atconn = check_attenuator_connect(attipstr, tprt)
            if atconn:
                self.progressBar_Att.setValue(50)  # ===================================================> 50%
            for attchn in att_chnl_lst:
                cA = read_str_value_from_attenuator_channel(attipstr, int(attchn))
                if cA:
                    if (int(cA) >= 0 and
                       int(cA) < 64):
                        self.progressBar_Att.setValue(100)  # ==================================================> 100%
                    logger.info(
                        '---------------: AttenuatorConnect to ' + attipstr + ' Ch.' + attchn + ', att.value = ' + cA)
                    self.statusBar().setStyleSheet("background-color : lightgreen")
                    self.statusBar().showMessage('Connected to Attenuator ' + attipstr + ' Ch.'
                                                 + attchn + ', att.value = ' + cA, 20000)
                else:
                    self.progressBar_Att.setValue(0)  # =====================================================> 0%
                    logger.info(
                        '---------------: AttenuatorConnect to ' + attipstr + ' Ch.' + attchn + ', att.value = ' + cA)
                    self.statusBar().setStyleSheet("background-color : red")
                    self.statusBar().showMessage('CANNOT read Attenuator ' + attipstr + ' Ch.' + attchn, 20000)
                QtWidgets.qApp.processEvents()  # Cycle Renew
        else:
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('No Att. channels', 20000)
            # Message Box "Attenuator's IP unreachable"
            self.display_message_box(QtWidgets.QMessageBox.Warning, 'Warning!', "Attenuator's IP unreachable")
            QtWidgets.qApp.processEvents()  # Cycle Renew
            return

    def AttenuatorDisconnect(self):
        logger.debug('---------------: call AttenuatorDisconnect')
        attipstr = self.lineEdit_Att_IP.text()
        disconnect_attenuator_main(attipstr)
        self.progressBar_Att.reset()
        logger.info('---------------: Attenuator disconnect from ' + attipstr)
        atconn = False
        self.statusBar().setStyleSheet("background-color : pink")
        self.statusBar().showMessage('Attenuator ' + attipstr + ' disconnected', 20000)

    def sshConnect(self):
        global sshipstr
        global sshport
        global sshpwd
        global IPERF3_PORT
        global L_iperfsrvrs_versions

        if IPERF3_PORT != int(self.lineEdit_iperf_port.text()):
            logger.info(f'Iperf base port changed to {self.lineEdit_iperf_port.text()}')
            IPERF3_PORT = int(self.lineEdit_iperf_port.text())

        # p =[] # 
        # self.iperf_srvr_log_lst = [] # clear iperf server list (ssh log)
        logger.debug('---------------: call sshConnect')
        sshipstr = self.lineEdit_ssh_IP.text()
        sshport = '22'
        sshname = self.lineEdit_ssh_Uname.text()
        sshpwd = self.lineEdit_ssh_Pwd.text()
        self.progressBar_ssh.reset()
        self.comboBox_2.setCurrentIndex(self.common_index)  # at fisrst, set to common
        self.progressBar_ssh.setValue(10)  # =====================================================> 10%
        if not check_self_ping_to(sshipstr):  # check server reachability using ping cmd
            self.progressBar_ssh.setValue(0)  # =====================================================> 0%
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('SSH server ' + sshipstr + 'unreachable', 10000)
            # Message Box "Server unreachable"
            txt = "Server " + sshipstr + " unreachable, check entered IP address or try another one!"
            self.display_message_box(QtWidgets.QMessageBox.Warning, 'Warning!', txt)
            return
        self.statusBar().setStyleSheet("background-color : lightgreen")
        self.statusBar().showMessage('SSH server ' + sshipstr + ' is reachable', 10000)
        self.progressBar_ssh.setValue(20)  # =====================================================> 20%
        QtWidgets.qApp.processEvents()  # Cycle Renew

        sshres, p = ssh_connect_main(sshipstr, sshport, sshname, sshpwd)  # check connect by Uname cmd
        if not sshres:
            txt = "Server " + sshipstr + " cannot be connected, check credentials"
            self.display_message_box(QtWidgets.QMessageBox.Warning, 'Warning!', txt)
            logger.info('---------------: Connect to ssh server ' + sshipstr + ' : ' + sshport +
                        ' is not successfull')
            logger.info('---------------: User: ' + sshname + ' Password: ' + sshpwd)
            logger.info('---------------: Data: ' + str(p))
            self.progressBar_ssh.setValue(0)  # =====================================================> 0%
            self.statusBar().setStyleSheet("background-color : red")
            self.statusBar().showMessage('SSH server ' + sshipstr + ' : ' + sshport
                                         + ' is not connected, Iperf server is not started!')
            self.comboBox_2.setCurrentIndex(self.common_index)
            return
        logger.info('---------------: Connect to ssh server ' + sshipstr + ':22')
        logger.info('---------------: User: ' + sshname + ' Password: ' + sshpwd)


        self.iperf_srvr_log_lst.extend(p)  # log file extend
        self.kill_iperfs_set()  # ----------------------------------> dialog for selection runned iperf
                                                                     # instances and kill selected pocesses

        self.progressBar_ssh.setValue(30)  # =====================================================> 30%
        self.Get_iperfs_list_from_server(sshipstr, sshport, sshname, sshpwd)  # get list of
                                                            # iperf executables on server to choose version
                                                            # and run selected version as server daemons
        self.progressBar_ssh.setValue(60)  # =====================================================> 60%

        self.L_iperfsrvrs_versions = [] # List of versions corresponed to list of found binaries in self.L_iperfsrvrs
        for ss in self.L_iperfsrvrs:
            [p1, e1] = exec_linux_command(ss.replace('\n', '') + ' -v')
            self.iperf_srvr_log_lst.extend(['> '+ss+' -v'])
            self.iperf_srvr_log_lst.extend(p1)  # log file extend
            self.iperf_srvr_log_lst.extend(e1)  # log file extend
            ver = None
            if ((p1  == '' or p1 == []) and (e1 != '' or e1 ==[])):
                p1.extend(e1) #  p1 = stdin + stdout
            if re.search(r'iperf version \d',p1[0]):
                ver = get_value_from_string(p1[0], 'iperf version ',' ')
            if ver:
                self.L_iperfsrvrs_versions.append(ver)
            else:
                if re.search(r'iperf \d',p1[0]):
                    ver = get_value_from_string(p1[0], 'iperf ', ' ')
                    if ver:
                        self.L_iperfsrvrs_versions.append(ver)
                    else:
                        self.L_iperfsrvrs_versions.append('unknown')
            L_iperfsrvrs_versions = self.L_iperfsrvrs_versions  # ==> global
            logger.debug(f'---------------: iperf version:{p1}')
            logger.debug(f'---------------: iperf ver#{ver}')
        self.run_iperfs_set()
        self.progressBar_ssh.setValue(100)  # =====================================================> 100%
        self.statusBar().setStyleSheet("background-color : lightgreen")
        self.statusBar().showMessage('SSH server ' + sshipstr + ':22 connected', 30000)
        self.comboBox_2.setCurrentIndex(self.iperf_index)


    def sshDisconnect(self):
        logger.debug('---------------: call sshDisconnect')
        self.comboBox_2.setCurrentIndex(self.common_index)
        sshipstr = self.lineEdit_ssh_IP.text()
        p1 = []
        if check_self_ping_to(sshipstr):  # check server reachability using ping cmd
            p1 = ssh_disconnect_main(sshipstr)  # may be add kill iperf -s -D with latest -p (???)
        else:
            p1.append('Server ' + sshipstr + ' is unreachable now!')
        self.progressBar_ssh.reset()
        logger.info('---------------: disconnect from ssh server ' + sshipstr)
        self.iperf_srvr_log_lst.extend(p1)
        self.statusBar().setStyleSheet("background-color : pink")
        self.statusBar().showMessage('Iperf server closed. SSH server ' + sshipstr + ':22 disconnected.', 20000)
        self.comboBox_2.setCurrentIndex(self.iperf_index)


    def display_iperf_client_output(self,data_str:str):
        ''' Display data_str in the textedit_1

        :param data_str: data string for output/display
        :return: none
        '''
        global outlst
        outlst.append(data_str)  # ==================> for processing
        self.iperf_clnt_lst.append(data_str)  # ==================>  to GUI
        self.textEdit_1.append(data_str)  # ==================>  to GUI directly
        # self.textEdit_1.verticalScrollBar().setValue(0) # OK
        self.textEdit_1.verticalScrollBar().setValue(self.textEdit_1.verticalScrollBar().maximum())  # OK
        QtWidgets.qApp.processEvents()  # events processing


    def run_iperf_clnt_interactive(self, cmd, title = 'undefined test'):
        ''' Intereactively run iperf client cmd via adb shell with redirect stdout to the textEdit_1 list
        cmd:str iperf client command
        title:str title display before client start
            Signals imported from module "signal" that can be used for break:
                CTRL_BREAK_EVENT = <Signals.CTRL_BREAK_EVENT: 1>
                CTRL_C_EVENT = <Signals.CTRL_C_EVENT: 0>
                NSIG = 23
                SIGABRT = <Signals.SIGABRT: 22>
                SIGBREAK = <Signals.SIGBREAK: 21>
                SIGFPE = <Signals.SIGFPE: 8>
                SIGILL = <Signals.SIGILL: 4>
                SIGINT = <Signals.SIGINT: 2>
                SIGSEGV = <Signals.SIGSEGV: 11>
                SIGTERM = <Signals.SIGTERM: 15>
                SIG_DFL = <Handlers.SIG_DFL: 0>
                SIG_IGN = <Handlers.SIG_IGN: 1>
            Manual break for iperf client realized without signal sending to process, but by kill client process
            Timeout watchdog for iperf client uses WatchdogTimer class, it kill the client process in case of timeout.
        '''
        global outlst
        logger.info('---------------: called run_iperf_clnt_interactive()' '> ' + cmd)
        outlst = []  # log
        tested_connection_RM = '' # 1/2/3=wifi
        tested_connection_RT = '' # GSM/WCDMA/LTE/NR/wifi
        tested_connection_ip = '' # mIP /wIP
        tested_connection_signal = ''  # RSSI /RSRP/ssRSRP
        tested_connection_Freq = ''
        tested_connection_BW = ''
        title_add = ''
        if DevModel:
            if devdata[0]['mIP'] !='': # If mIP present, check RMs:
                for i in range(RMq):
                    if 'IN_SERVICE' in devdata[i]['mRegPS']: # if PS in service for RM
                        tested_connection_ip = devdata[0]['mIP'] # it's IP of this RM
                        tested_connection_RM = str(i)
                        iRM = i # connected Radio Module '0'/'1' of mIP
                        if ((devdata[i]['mRATC'] == 'LTE'
                               or 'Lte' in (devdata[i]['RTech'])) # if LTE connection
                               and devdata[i]['ssRsrp'] !='N/A'
                               and devdata[i]['ssRsrp'] is not None): # and NR signal present # ToDo:
                            tested_connection_RT = 'NR'           # it is an NR connection
                            tested_connection_signal = devdata[i]['ssRsrp'] # NR connection signal
                        else: # if it ids not NR connection:
                            if ( devdata[i]['mRATC'] == 'LTE'
                               or 'Lte' in (devdata[i]['RTech'])): # if it's LTE connection:
                                tested_connection_RT = devdata[i]['RTech']
                                tested_connection_signal = devdata[i]['RSRP']
                                tested_connection_Freq = devdata[i]['mChan']
                                tested_connection_BW = devdata[i]['mBW']
                            elif devdata[i]['mRATC'] == 'UMTS': # if it's UMTS connection:
                                tested_connection_signal = devdata[i]['RSCP']
                                tested_connection_RT = devdata[i]['mRATC'] + '(' +valfrombrackets(devdata[i]['mPSRT']) + ')'
                            elif devdata[i]['mRATC'] == 'GSM': # if it's GSM connection:
                                tested_connection_signal = devdata[i]['RSSI']
                            else: # unknown connection or no connection:
                                tested_connection_RT = 'No connection'
                                tested_connection_signal = 'No signal'

                        # if 'UNKNOWN' not in devdata[i]['mRATC']:
                        #     if tested_connection_RT == '':
                        #             tested_connection_RT = devdata[i]['mRATC']
                #         else: # if not In Service (another RM or WiFi?)
                #             continue # next RM
                    elif devdata[0]['wIP'] !='': # no mIP, but wIP present ==> WiFi connection:
                        tested_connection_ip = devdata[0]['wIP']
                        iRM = 3
                        tested_connection_RM = 'WiFi'
                        tested_connection_RT = 'WiFi'
                        tested_connection_ip = devdata[0]['wIP']
            ### RMs cycle finished
            if tested_connection_ip == '': # if ip not foud in cycle
                if devdata[0]['wIP'] !='': # then it is WiFi ip
                    # if 'IWLAN' in devdata[0]['mRATC']:
                    tested_connection_RM = 'WiFi'
                    tested_connection_RT = 'WiFi'
                    tested_connection_ip = devdata[0]['wIP']
                    tested_connection_signal = devdata[0]['wRSSI']

            logger.info(f'Radio Module: {tested_connection_RM}')
            logger.info(f'Radio Technology = {tested_connection_RT}')
            logger.info(f'RadioModule IP   = {tested_connection_ip}')
            if (tested_connection_RT == 'IWLAN'
                or tested_connection_RT == 'WiFi'): # is 'IWLAN' always means WiFi??? ToDo:
                tested_connection_link_speed = devdata[0]['WiFi_link_speed']
                tested_connection_rx_link_speed = devdata[0]['WiFi_RX_link_speed']
                tested_connection_tx_link_speed = devdata[0]['WiFi_TX_link_speed']
                tested_connection_wifi_gen = devdata[0]['WiFi_Generation']
                title_add = f'Technology = {tested_connection_RT}, RSSI = {tested_connection_signal}dBm, ' \
                            f'WiFi Link = {tested_connection_link_speed}, \nWiFi Tx = {tested_connection_tx_link_speed}, ' \
                            f'WiFi Rx = {tested_connection_rx_link_speed}, WiFi Gen.:{tested_connection_wifi_gen}'
            elif tested_connection_RT == 'LTE':
                title_add = f'Radio Module:{tested_connection_RM}, Technology: {tested_connection_RT}, RSRP = {tested_connection_signal}dBm, ' \
                            + f'ARFCN: {tested_connection_Freq}, Bandwith: {tested_connection_BW} kHz'
            elif tested_connection_RT == 'NR':
                title_add = f'Radio Module:{tested_connection_RM}, Technology: {tested_connection_RT}, ssRSRP = {tested_connection_signal}dBm, '
            elif 'UMTS' in tested_connection_RT:
                title_add = f'Radio Module:{tested_connection_RM}, Technology = {tested_connection_RT}, RSCP = {tested_connection_signal}dBm'
            else:
                title_add = f'Radio Module:{tested_connection_RM}, Technology = {tested_connection_RT}, RSSI = {tested_connection_signal}dBm'
        else:
            title_add = 'ADB is not connected, Radio Module:UNKNOWN, Technology = UNKNOWN, SIGNAL LEVEL = UNKNOWN'

    ### title output (bigger font size)
        self.textEdit_1.setTextBackgroundColor(self.whiteColor)
        if self.checkBox_L1_exp.checkState():
            self.textEdit_1.setFontPointSize(16)
            self.textEdit_1.setFont(QFont("Consolas",16, QFont.Bold))
        else:
            self.textEdit_1.setFontPointSize(9)
            self.textEdit_1.setFont(QFont("Consolas", 9, QFont.Bold))
        self.display_iperf_client_output(title + title_add)
    ### cmd output
        if self.checkBox_L1_exp.checkState():
            fs = 10
        else:
            fs = 8
        self.textEdit_1.setFontPointSize(fs)
        self.textEdit_1.setFont(QFont("Consolas",fs, QFont.Normal ))
        self.display_iperf_client_output('>'+cmd)
        self.textEdit_1.setFontPointSize(fs)
        fs = 10 if self.checkBox_L1_exp.checkState() else 7
        # if self.checkBox_L1_exp.checkState():
        #     fs = 10
        # else:
        #     fs = 7
        QtWidgets.qApp.processEvents()  # events processing

        # watchdog run
        self.watchdog_type = True # True for Watchdog class, False for QTimer
        self.periodic_iperf_client_timer_start()
        logger.info(f'---------------: Watchdog timer started for {self.iperf_current_timeout_value} sec.')
        process = Popen(cmd, stdout=PIPE, stderr=STDOUT, shell=True, universal_newlines=True,bufsize=1) # , shell=True
        # try:
        for output in process.stdout:
            # Break signal handler
            if self.iperf_break:
                self.periodic_iperf_client_timer_stop()
                break_str = '----------------------------------------------[Break]----------------------------------------------'
                logger.info(break_str)
                # self.textEdit_1.setTextBackgroundColor(self.lightredColor)
                self.display_iperf_client_output(colored_text(break_str, col_val='#800000', weight=600))
                # self.textEdit_1.setTextBackgroundColor(self.whiteColor)
                res_kill = thr_res_kill_iperfs_clients = threading.Thread(target = kill_iperf_clients,
                                        args=(self.iperf_version,)).start() # kill iperf_x process at Android device
                res_kill = self.kill_iperf_client() # kill iperf_x process at Android device
                self.display_iperf_client_output(f'Kill process result:{res_kill}')
                process.kill()  # kill windows subprocess of adb shell
                self.iperf_break = False  # reset signal
                return outlst  # ==================> for processing
            print(output.strip('\n'))  # ======================> to client list view in console
            # watchdog reset
            self.periodic_iperf_client_timer_restart()
            logger.info(f'---------------: Watchdog timer restarted.')

            self.textEdit_1.setFont(QFont("Consolas", fs, QFont.Normal))
            # self.textEdit_1.setTextBackgroundColor(self.whiteColor)
            if ('SUM' in output
                and 'receiver' in output):
                self.textEdit_1.setTextBackgroundColor(self.yellowColor)
                self.display_iperf_client_output(output.strip('\n'))
            elif 'receiver' in output:
                self.textEdit_1.setTextBackgroundColor(self.greenyellowColor)
                self.display_iperf_client_output(output.strip('\n'))
            elif ('SUM' in output
                and 'omit' not in output
                and 'order' not in output):
                # self.display_iperf_client_output(colored_text(output.strip('\n'), col_val='#008000', weight=600))
                self.textEdit_1.setTextBackgroundColor(self.lightgreenColor)
                self.display_iperf_client_output(output.strip('\n'))
            else:
                self.textEdit_1.setTextBackgroundColor(self.whiteColor)
                self.display_iperf_client_output(output.strip('\n'))
        break_str = '================================================= iperf done ================================================='
        logger.info(break_str)
        self.textEdit_1.setTextBackgroundColor(self.whiteColor)
        self.display_iperf_client_output(break_str)
        # watchdog stop
        self.periodic_iperf_client_timer_stop()
        logger.info(f'---------------: Watchdog timer stopped.')
        return outlst


    def init_iperf_clnt__data(self):
        """ Construct iperf client command string for required parameters to run it on the DUT
        """
        global IPERF3_PORT, IPERF2_PORT_TCP, IPERF2_PORT_UDP
        IPERF2_PORT_TCP = IPERF3_PORT + 10
        IPERF2_PORT_UDP = IPERF3_PORT + 20
        self.iperf_break = False # no break signal at start
        if not self.checkBox_L1_exp.checkState():
            self.checkBox_L1_exp.setChecked(True)
        iperf_tcp_time = self.lineEdit_iperf_tcp_time.text()
        iperf_tcp_sessions = self.lineEdit_iperf_tcp_sessions.text()
        iperf_udp_time = self.lineEdit_iperf_udp_time.text()
        iperf_udp_bandwith = self.lineEdit_iperf_udp_bandwith.text()
        logger.info(f'SUM = {self.checkBox_sum.checkState()}')
        logger.info(f'Flush = {self.checkBox_flush.checkState()}')
        if sshclient and sshconn:
            # else:
            if (iperf_tcp_time != 'sec' and
                self.lineEdit_iperf_tcp_sessions.text() != 'sess' and
                iperf_udp_time != 'sec' and
                self.lineEdit_iperf_udp_bandwith.text() != 'Mbps'):
                iperf_clnt_ip = ' -c ' + sshipstr
                if self.iperf_version == 3: # iperf3
                    iperf_client_udp_cmd0 = torun + 'shell '      + iperf_clnt_path + iperf3_version + iperf_clnt_ip
                    iperf_client_tcp_cmd0 = torun + 'shell '+ '"' + iperf_clnt_path + iperf3_version + iperf_clnt_ip
            # works for Windows better (w/o buffering) than grep in Android for dynamical output, required shell=True
                    iperf_client_threads = '" | find "SUM' if self.checkBox_sum.checkState() else ''
            # huge (stdout buffering) but works without shell=True
                    # iperf_client_threads = ' | grep SUM' if self.checkBox_sum.checkState() else ''
                    iperf_clnt_option = ' --forceflush ' if self.checkBox_flush.checkState() else ''
                    iperf_tcp1 = iperf3_tcp0 + ' -p' + self.lineEdit_iperf_port.text() + iperf_clnt_option
                    iperf_udp1 = iperf3_udp0 + ' -p' + self.lineEdit_iperf_port.text() + iperf_clnt_option
                else: #iperf2
                    iperf_client_udp_cmd0 = torun + 'shell '      + iperf_clnt_path + iperf2_version + iperf_clnt_ip
                    iperf_client_tcp_cmd0 = torun + 'shell '+ '"' + iperf_clnt_path + iperf2_version + iperf_clnt_ip
                    iperf_client_threads = ' --sum-only' if self.checkBox_sum.checkState() else ''
                    iperf_clnt_option = ' -e '  if self.checkBox_flush.checkState() else '' # for iperf2 use option -e
                                 # instead of --flush of iperf3 (for flushing buffer) with control by the same checkbox
                    iperf_tcp1 = iperf2_tcp0 + ' -p' + str(int(self.lineEdit_iperf_port.text()) + 10) + iperf_clnt_option
                    iperf_udp1 = iperf2_udp0 + ' -p' +  str(int(self.lineEdit_iperf_port.text()) + 20) + iperf_clnt_option
                sess_add = (' -P' + iperf_tcp_sessions + iperf_client_threads + '"'
                            if iperf_tcp_sessions not in ["0","1", ""] else '"')
                iperf_client_cmd_tcp_base = (iperf_client_tcp_cmd0 + ' -t' + iperf_tcp_time + iperf_tcp1)
                self.iperf_client_cmd_tcp_ul = (iperf_client_cmd_tcp_base + sess_add)
                self.iperf_client_cmd_tcp_dl = (iperf_client_cmd_tcp_base + ' -R ' + sess_add)
                if self.iperf_version == 3: # iperf3
                    self.iperf_client_cmd_tcp_bi = (iperf_client_cmd_tcp_base + ' --bidir ' + sess_add)
                else:
                    self.iperf_client_cmd_tcp_bi = (iperf_client_cmd_tcp_base + ' -d  ' + sess_add)  # using two unidirectional sockets
                    # self.iperf_client_cmd_tcp_bi = (iperf_client_cmd_tcp_base + ' --full-duplex ' + sess_add)  # full duplex test using same socket

                iperf_client_cmd_udp_base = (iperf_client_udp_cmd0 + iperf_udp1 + ' -t' + iperf_udp_time
                                             + ' -b' + iperf_udp_bandwith + 'M ')
                self.iperf_client_cmd_udp_ul = (iperf_client_cmd_udp_base )
                self.iperf_client_cmd_udp_dl = iperf_client_cmd_udp_base + ' -R '     # + '"'
                if self.iperf_version == 3: # iperf3
                    self.iperf_client_cmd_udp_bi = iperf_client_cmd_udp_base + ' --bidir'  # + '"'
                else:
                    self.iperf_client_cmd_udp_bi = iperf_client_cmd_udp_base + ' -d  ' + sess_add  # full duplex test using same socket
                    # self.iperf_client_cmd_udp_bi = iperf_client_cmd_udp_base + ' --full-duplex'  # + '"'
                self.wrong_input = False
                return
            logger.error('|----------------------------- Wrong input iperf client parameters')
            self.display_message_box (2, 'Warning', 'Check iperf client parameters!')
            self.wrong_input = True
            return
        # else:
        logger.error('|----------------------------- SSH server is not connected!')
        self.display_message_box(2, 'Warning', 'Please, connect to the SSH server!')
        self.wrong_input = True
        return

    def run_iperfclnt_tcp_UL(self):
        self.init_iperf_clnt__data()
        if self.wrong_input:
            return
        self.comboBox_1.setCurrentIndex(self.iperf_index)
        iperf_clnt_cmd = self.iperf_client_cmd_tcp_ul

        out = self.run_iperf_clnt_interactive(iperf_clnt_cmd, f'Iperf {self.iperf_version}  UL TCP throughput: \n')

# results to be processed
        print('================================================RESULTS================================================')
        for s in out:
            print(s)
        print()

    def run_iperfclnt_tcp_DL(self):
        self.init_iperf_clnt__data()
        if self.wrong_input:
            return
        self.comboBox_1.setCurrentIndex(self.iperf_index)
        iperf_clnt_cmd = self.iperf_client_cmd_tcp_dl
        out = self.run_iperf_clnt_interactive(iperf_clnt_cmd,f'Iperf {self.iperf_version}  DL TCP throughput: \n')
        print('================================================RESULTS===============================================')
        for s in out:
            print(s)
        print()        

    def run_iperfclnt_tcp_BiDi(self):
        self.init_iperf_clnt__data()
        if self.wrong_input:
            return
        self.comboBox_1.setCurrentIndex(self.iperf_index)
        iperf_clnt_cmd = self.iperf_client_cmd_tcp_bi
        out = self.run_iperf_clnt_interactive(iperf_clnt_cmd,f'Iperf {self.iperf_version}  BiDirectional TCP throughput: \n')
        print('================================================RESULTS==============================================')
        for s in out:
            print(s)
        print()

    def run_iperfclnt_udp_UL(self):
        self.init_iperf_clnt__data()
        if self.wrong_input:
            return
        self.comboBox_1.setCurrentIndex(self.iperf_index)
        iperf_clnt_cmd = self.iperf_client_cmd_udp_ul
        out = self.run_iperf_clnt_interactive(iperf_clnt_cmd,f'Iperf {self.iperf_version}  UL UDP throughput: \n')
        print('================================================RESULTS================================================')
        for s in out:
            print(s)
        print()

    def run_iperfclnt_udp_DL(self):
        self.init_iperf_clnt__data()
        if self.wrong_input:
            return
        self.comboBox_1.setCurrentIndex(self.iperf_index)
        iperf_clnt_cmd = self.iperf_client_cmd_udp_dl
        out = self.run_iperf_clnt_interactive(iperf_clnt_cmd,f'Iperf {self.iperf_version}  DL UDP throughput: \n')
        print('================================================RESULTS===============================================')
        for s in out:
            print(s)
        print()

    def run_iperfclnt_udp_BiDi(self):
        self.init_iperf_clnt__data()
        if self.wrong_input:
            return
        self.comboBox_1.setCurrentIndex(self.iperf_index)
        iperf_clnt_cmd = self.iperf_client_cmd_udp_bi
        out = self.run_iperf_clnt_interactive(iperf_clnt_cmd,f'Iperf {self.iperf_version}  BiDirectional UDP throughput: \n')
        print('================================================RESULTS==============================================')
        for s in out:
            print(s)
        print()


    def List3Update(self,s):
        logger.debug(f'---------------: call List3Update {str(s)}')
        logger.info(s)
        for i in range(len(servers)):
            if s in servers[i][1]:
                logger.info(str(i)+str(servers[i]))
                self.lineEdit_ssh_IP.setText(servers[i][0])
                self.lineEdit_ssh_Uname.setText(servers[i][2])
                self.lineEdit_ssh_Pwd.setText(servers[i][3])
                break


    def List1Update(self, s):
        logger.debug(f'---------------: call List1Update {str(s)}')
        if 'IP info' in s:
            self.clearRecs_l1()
            self.textEdit_1.setTextBackgroundColor(self.whiteColor)
            self.append_recs_ip_info_l1()
            self.textEdit_1.verticalScrollBar().setValue(0)
        elif 'WiFi scanner' in s:
            self.clearRecs_l1()
            if DevModel:
                self.progressBar_ADB.setValue(50)  # =============> 50%
                get_wifi_scanner_data_main()
                self.progressBar_ADB.setValue(100)  # ============> 100%
            else:
                self.progressBar_ADB.setValue(0)  # =============> 0%
            self.append_recs_wifi_scan_data_l1()
            QtWidgets.qApp.processEvents()  # Cycle Renew

        elif 'Disk info' in s:
            self.clearRecs_l1()
            self.append_recs_disk_info_l1()
        elif 'WiFi info' in s:
            self.clearRecs_l1()
            self.append_recs_wifi_info_l1()
        elif 'Battery info' in s:
            self.clearRecs_l1()
            self.textEdit_1.setTextBackgroundColor(self.whiteColor)
            self.append_recs_bat_info_l1()
        elif 'RAM info' in s:
            self.clearRecs_l1()
            self.appendRecs1013()
        elif 'Connection' in s:
            self.clearRecs_l1()
            self.append_records_lst_l1()
        elif 'pkg' in s:
            self.clearRecs_l1()
            self.append_recs_pkg_installation_l1()
        elif 'apk' in s:
            self.clearRecs_l1()
            self.append_recs_apk_installation_l1()
        elif 'Iperf' in s:
            self.clearRecs_l1()
            self.append_recs_iperf_client_l1()
        else:
            self.clearRecs_l1()
            self.append_records_lst_l1()
        QtWidgets.qApp.processEvents()  # Cycle Renew

    def List2Update(self, s):
        logger.debug(f'---------------: call List2Update  {str(s)}')
        if 'IP info' in s:
            self.clearRecs_l2()
            self.textEdit_2.setTextBackgroundColor(self.whiteColor)
            self.append_recs_ip_info_l2()
        elif 'WiFi scanner' in s:
            if DevModel:
                self.clearRecs_l2()
                self.progressBar_ADB.setValue(50)  # =============> 50%
                get_wifi_scanner_data_main()
                self.progressBar_ADB.setValue(100)  # ============> 100%
            else:
                self.progressBar_ADB.setValue(0)  # =============> 0%
            self.append_recs_wifi_scan_data_l2()
            QtWidgets.qApp.processEvents()  # Cycle Renew
        elif 'Disk info' in s:
            self.clearRecs_l2()
            self.append_recs_disk_info_l2()
        elif 'WiFi info' in s:
            self.clearRecs_l2()
            self.append_recs_wifi_info_l2()
        elif 'Battery info' in s:
            self.clearRecs_l2()
            self.textEdit_2.setTextBackgroundColor(self.whiteColor)
            self.append_recs_bat_info_l2()
        elif 'RAM info' in s:
            self.clearRecs_l2()
            self.appendRecs1013_l2()
            self.textEdit_2.verticalScrollBar().setValue(0)
        elif 'Connection' in s:
            self.clearRecs_l2()
            self.append_records_lst_l2()
        elif 'pkg' in s:
            self.clearRecs_l2()
            self.append_recs_pkg_installation_l2()
        elif 'apk' in s:
            self.clearRecs_l2()
            self.append_recs_apk_installation_l2()
        elif 'Iperf' in s:
            self.clearRecs_l2()
            self.append_recs_iperf_server_l2()
        else:
            self.clearRecs_l2()
            self.append_records_lst_l2()
        QtWidgets.qApp.processEvents()  # Cycle Renew

############################################################################################
############################################################################################
############################################################################################
def check_adb_installed():
    # Check ADB installed
    if not os.path.exists(torun):  # if file  'c:\adb\adb.exe' is not exist
        logger.error('ADB tool is not found at %s', torun)
        display_critical_message(2, 'ADB is not installed','<center> Please, install ADB tool first</center>')
        return False
    else:
        logger.info('ADB tool found at ' + torun)
        return True
    
def display_critical_message(icon:int, title:str, msg:str):
# Message Box
    app = QtWidgets.QApplication(sys.argv)
    win = QtWidgets.QMainWindow()
    win.setGeometry(500, 500, 500, 500)
    msg = QtWidgets.QMessageBox(win)
    msg.setWindowTitle(title)
    msg.setText(msg)
    msg.setIcon(QtWidgets.QMessageBox.Critical)
    msg.exec_()

def get_servers_data(filename: str):
    ''' configuration file example
        ----------------------------------------------------------------------------------------------------------------
           0        1    2  3
    0    Defaults:; --; --;--
    1    ADB path;c:\\adb\\adb.exe; iperf3port;5400
    2    iperf_clnt_path;/data/local/tmp/;iperf_clnt_path2;'/data/local/tmp/'
    3    iperf2_version;iperf2.1.4; iperf3_version;iperf3.7
    4    iperf3_srvr_params;-s -D ; iperf3_tcp0; -i1 -w400K  -O2 -p
    5    iperf2_srvr_tcp_params;-s -e -D -w16M ; iperf2_tcp0; -i1 -w16M -p
    6    iperf2_srvr_udp_params;-s -D -w16M -u ; iperf_srvr_cmd2chk;iperf
    7    iperf3_udp0; -u -i1 -O2 -p; iperf2_udp0; -u -i1 -w16M -p

    8    Servers:; --; --;--
    9    10.10.30.3;ubt-srv-ftp1;testuser;q1w2e3r4
    10    10.10.30.4;ubt-srv-ftp2;testuser;q1w2e3r4
    11    192.168.1.32;HOME_notebook;testuser;q1w2e3r4
    12    10.2.191.62;temp_notebook#1;testuser;q1w2e3r4
    13    10.2.191.68;temp_notebook#2;testuser;q1w2e3r4
          ......
          End of file;end;end;end
        ----------------------------------------------------------------------------------------------------------------
    :param filename:
    :return: global vars: servers, iperf parameters etc.
    '''
    global servers, IPERF3_PORT, IPERF2_PORT_TCP, IPERF2_PORT_UDP, torun, \
        iperf_clnt_path, iperf_clnt_path2, iperf2_version, iperf3_version,\
        iperf3_srvr_params, iperf3_tcp0, iperf2_srvr_tcp_params, iperf2_tcp0,\
        iperf2_srvr_udp_params, iperf_srvr_cmd2chk, iperf3_udp0, iperf2_udp0,servers_csv_count, TIMEOUT_IPERF_CLIENT
    with open(filename, encoding='utf-8') as r_file:
        file_reader = csv.reader(r_file, delimiter=";")
        count = 0
        servers_csv_count = 0
        Servers_flag = False

        for row in file_reader:
            if not Servers_flag:
                if count == 0 :
                    if 'Defaults:' not in row[0]:
                        logger.error(f'configuration file {filename} inconsistent, using script default values')
                        # return  servers_csv_count
                    else:
                        if 'timeout_iperf_client' in row[2]:
                            TIMEOUT_IPERF_CLIENT = int(row[3])
                            logger.info(f'Watchdog timer for iperf client set to:  {TIMEOUT_IPERF_CLIENT} sec.')
                        count += 1
                        continue
                if 'ADB path' in row[0]:
                    if 'adb.exe' in row[1]:
                        torun = row[1].replace('"','')+' '
                        logger.info(f'ADB path: {torun}')
                    if 'iperf3port' in row[2]:
                        IPERF3_PORT = int(row[3])
                        IPERF2_PORT_TCP = IPERF3_PORT + 10
                        IPERF2_PORT_UDP = IPERF3_PORT + 20
                        logger.info(f'iperf3 base port = {IPERF3_PORT}')
                elif ('iperf_clnt_path' in row[0] and 'iperf_clnt_path2' in row[2]):
                    iperf_clnt_path = row[1]
                    iperf_clnt_path2 = row[3]
                    pass
                elif ('iperf2_version' in row[0] and 'iperf3_version' in row[2]):
                    iperf2_version = row[1]
                    iperf3_version = row[3]
                elif ('iperf3_srvr_params' in row[0] and 'iperf3_tcp0' in row[2]):
                    iperf3_srvr_params = row[1]
                    iperf3_tcp0 = row[3]
                elif ('iperf2_srvr_tcp_params' in row[0] and 'iperf2_tcp0' in row[2]):
                    iperf2_srvr_tcp_params = row[1]
                    iperf2_tcp0 = row[3]
                elif ('iperf2_srvr_udp_params' in row[0] and 'iperf_srvr_cmd2chk' in row[2]):
                    iperf2_srvr_udp_params = row[1]
                    iperf_srvr_cmd2chk = row[3]
                elif ('iperf3_udp0' in row[0] and 'iperf2_udp0' in row[2]):
                    iperf3_udp0 = row[1]
                    iperf2_udp0 = row[3]
                elif 'Servers:' in row[0]:
                    Servers_flag = True
                    continue
            else:
                if 'End of file' in row[0]:
                    break
                else:
                    servers.append([row[0],row[1],row[2],row[3]])
                    servers_csv_count +=1
            count += 1
        return servers_csv_count

def main():
    app_ADB = QtWidgets.QApplication(sys.argv)  # Новый экземпляр QApplication
    window_ADB_Main = ADB_App_Main()  # Создаём объект класса ADB_App
    window_ADB_Main.show()       # Показываем окно
    app_ADB.exec_()         # и запускаем приложение

############################################################################################
# MAIN
############################################################################################

#  Paramiko set-up
sshclient = paramiko.SSHClient()
sshclient.load_system_host_keys()
sshclient.set_missing_host_key_policy(paramiko.AutoAddPolicy())

# Logging set-up
loglev = logging.ERROR  # default
if len(sys.argv) > 1:
    if '--debug' in sys.argv[1]:
        loglev = logging.DEBUG
    elif '--info' in sys.argv[1]:
        loglev = logging.INFO
    else:
        loglev = logging.ERROR
else:
    loglev = logging.ERROR
formatter = '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
logging.basicConfig(level=loglev, format=formatter)
logger = logging.getLogger('_ADBproc')
logger.setLevel(loglev)
logger.debug('---------------: Logger initialized')


# read servers csv if present:
cwd = os.getcwd()  # текущий каталог
if os.path.exists(fn):
    servers_csv_count = get_servers_data(fn)
    logger.info(f'---------------: File {fn} found in {cwd} consist data of {servers_csv_count} servers')
    logger.info(f'iperf3 base port changed to: {IPERF3_PORT}')
else:
    logger.info(f'---------------: File {fn}  is not found in {cwd}')
    logger.info(f'iperf3 base port keep: {IPERF3_PORT}')

if (check_adb_installed() and 
       __name__ == '__main__'):
    main()

#####################################################################################################
# Notes:
#=======
# shell "dumpsys window | grep base="
#     init=1440x3200 600dpi base=1080x2400 420dpi cur=1080x2400 app=1080x2288 rng=1080x978-2327x2288
#
# fs = 10 # font size
#
# redText = f"<span style=\"  font-weight:1000; color:#800000;\" >"  # font-size:{fs}pt;
# redText.append(output.strip('\n')).append("</span>")
# redText += output.strip('\n') + "</span>"
# self.display_iperf_client_output(redText)
#
# blackText = f"<span style=\" font-weight:1000; color:#000000;\" >"  # font-size:{fs}pt;
# blackText.append('').append("</span>")
# blackText += '' + "</span>"
# self.display_iperf_client_output(blackText)
#
# self.textEdit_1.setFont(QFont("Consolas", fs, QFont.Normal))
# self.textEdit_1.setFont(QFont("Consolas", fs, QFont.DemiBold))
# self.textEdit_1.setFont(QFont("Consolas", fs, QFont.Bold))
# self.textEdit_1.setFont(QFont("Consolas", fs, QFont.Normal))
#
# self.textEdit_1.setFontUnderline(True)
# self.textEdit_1.setFontUnderline(False)
#
# self.textEdit_2.verticalScrollBar().setValue(0)  # OK
# self.textEdit_2.verticalScrollBar().setValue(self.textEdit_2.verticalScrollBar().maximum()) # OK

# print(Qt.GlobalColor.darkYellow)
# self.textEdit_1.append(colored_text(lst_l1[row], col_val='#700000', weight=600))
# self.textEdit_2.setTextBackgroundColor(self.lightredColor)
# self.textEdit_2.setTextBackgroundColor(self.lightgreenColor)
