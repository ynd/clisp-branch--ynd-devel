;; Foreign functions provided by the win32 system libraries
;; Copyright (C) 2003-2007 Sam Steingold

(defpackage "WIN32"
  (:nicknames "WOE32" "W32")
  (:modern t)
  (:use "COMMON-LISP" "FFI")
  (:shadowing-import-from "EXPORTING"
    #:defconstant #:defun #:defmacro
    #:def-c-type #:def-c-enum #:def-c-struct #:def-c-var #:def-call-out))

(in-package "W32")

(default-foreign-language :stdc-stdcall) ; WINAPI means __stdcall
(eval-when (compile) (setq *foreign-guard* t))

(def-c-type handle c-pointer)
(def-c-type dword uint32)
(def-c-type word uint16)

;; this is not necessary: we are not creating a C file anyway
;; (and thus cannot use def-c-const instead of defconstant below!)
;;(c-lines "#define WINVER 0x0500~%#include <windows.h>~%")

;;; ==================================== "kernel32.dll"
(default-foreign-library "kernel32.dll")

(def-call-out GetCommandLineA (:return-type c-string) (:arguments))
(def-call-out GetLastError (:return-type dword) (:arguments))
(def-call-out GetCurrentProcess (:return-type handle) (:arguments))
(def-call-out GetCurrentThread (:return-type handle) (:arguments))
(def-call-out GetCurrentProcessId (:return-type dword) (:arguments))
(def-call-out GetProcessVersion (:return-type dword) (:arguments (pid dword)))
(def-call-out GetProcessId (:return-type dword) ; longhorn
  (:arguments (hProcess handle)))
(def-call-out GetCurrentThreadId (:arguments) (:return-type dword))
(def-call-out GetProcessIdOfThread (:return-type dword) ; longhorn
  (:arguments (hThread handle)))
(def-call-out GetThreadId (:return-type dword) ; longhorn
  (:arguments (hThread handle)))
(def-call-out GetThreadPriority (:return-type int)
  (:arguments (hThread handle)))
(def-call-out GetThreadPriorityBoost (:return-type boolean)
  (:arguments (hThread handle) (no-boost (c-ptr boolean) :out)))
(def-call-out GetProcessPriorityBoost (:return-type boolean)
  (:arguments (hProcess handle) (no-boost (c-ptr boolean) :out)))
(def-call-out CloseHandle (:return-type boolean) (:arguments (handle handle)))

(defmacro with-handle ((handle form) &body forms)
  (multiple-value-bind (body-rest declarations) (SYSTEM::PARSE-BODY forms)
    `(let ((,handle ,form))
       (declare (read-only ,handle) ,@declarations)
       (unwind-protect (progn ,@body-rest)
         (when ,handle (CloseHandle ,handle))))))

;; (c-lines "#include <winnt.h>~%")
(eval-when (compile eval load)
(def-c-enum RIGHTS
  (SYNCHRONIZE              #x100000)
  (STANDARD_RIGHTS_REQUIRED  #xF0000)
  (STANDARD_RIGHTS_READ	     #x20000)
  (STANDARD_RIGHTS_WRITE     #x20000)
  (STANDARD_RIGHTS_EXECUTE   #x20000)
  (STANDARD_RIGHTS_ALL      #x1F0000)
  (SPECIFIC_RIGHTS_ALL        #xFFFF)
  (ACCESS_SYSTEM_SECURITY  #x1000000)))

(def-c-enum PROCESS
  (PROCESS_TERMINATE             1)
  (PROCESS_CREATE_THREAD         2)
  (PROCESS_SET_SESSIONID         4)
  (PROCESS_VM_OPERATION          8)
  (PROCESS_VM_READ              16)
  (PROCESS_VM_WRITE             32)
  (PROCESS_DUP_HANDLE           64)
  (PROCESS_CREATE_PROCESS      128)
  (PROCESS_SET_QUOTA           256)
  (PROCESS_SET_INFORMATION     512)
  (PROCESS_QUERY_INFORMATION  1024)
  (PROCESS_ALL_ACCESS
   #.(cl:logior STANDARD_RIGHTS_REQUIRED SYNCHRONIZE #xFFF)))

(def-call-out OpenProcess (:return-type handle)
  (:arguments (access-flag dword) ; PROCESS
              (inherit-handle boolean)
              (pid dword)))

(eval-when (compile eval load)
  (defconstant BUFSIZ 4096)     ; <stdio.h>
  (defconstant MAX_PATH 260))   ; <windef.h>

(def-call-out GetModuleFileNameA (:return-type dword)
  (:arguments (application-instance-handle handle)
              (name (c-ptr (c-array-max character #.MAX_PATH)) :out :alloca)
              (size dword))) ; always pass MAX_PATH as the second argument

(def-call-out GetModuleHandleA (:return-type handle)
  (:arguments (name c-string)))

;; (c-lines "#include <winicon.h>~%")

(def-call-out GetConsoleTitleA (:return-type dword)
  (:arguments (buffer (c-ptr (c-array-max character #.BUFSIZ)) :out :alloca)
              (size dword)))   ; always pass BUFSIZ as the only argument

(def-call-out SetConsoleTitleA (:return-type boolean)
  (:arguments (title c-string)))

(def-call-out GetConsoleWindow (:return-type handle) (:arguments)
  (:documentation "http://msdn.microsoft.com/library/en-us/dllproc/base/getconsolescreenbufferinfo.asp"))

(def-c-struct SMALL_RECT (Left short) (Top short) (Right short) (Bottom short))
(def-c-struct COORD (X short) (Y short))
(def-c-struct CONSOLE_SCREEN_BUFFER_INFO
  (dwSize COORD) (dwCursorPosition COORD)
  (wAttributes word) (srWindow SMALL_RECT) (dwMaximumWindowSize COORD))

(def-call-out GetConsoleScreenBufferInfo (:return-type boolean)
  (:documentation "http://msdn.microsoft.com/library/en-us/dllproc/base/getconsolescreenbufferinfo.asp")
  (:arguments (StdHandle handle)
              (csbiInfo (c-ptr CONSOLE_SCREEN_BUFFER_INFO) :out :alloca)))

;; system information
(def-call-out GetSystemDirectoryA (:return-type uint)
  (:arguments (buffer (c-ptr (c-array-max character #.MAX_PATH)) :out :alloca)
              (size uint))) ; pass MAX_PATH
(def-call-out GetWindowsDirectoryA (:return-type uint)
  (:arguments (buffer (c-ptr (c-array-max character #.MAX_PATH)) :out :alloca)
              (size uint))) ; pass MAX_PATH

(def-call-out GetCurrentDirectoryA (:return-type dword)
  (:arguments (size dword) ; pass MAX_PATH
              (buffer (c-ptr (c-array-max character #.MAX_PATH)) :out :alloca)))
(def-call-out GetVersion (:return-type dword) (:arguments))

;;; i/o
(def-call-out GetStdHandle (:return-type handle)
  (:documentation "http://msdn.microsoft.com/library/en-us/dllproc/base/getstdhandle.asp")
  (:arguments (nStdHandle dword)))
(def-call-out SetStdHandle (:return-type boolean)
  (:documentation "http://msdn.microsoft.com/library/en-us/dllproc/base/setstdhandle.asp")
  (:arguments (nStdHandle dword) (hHandle handle)))

(defconstant STD_INPUT_HANDLE   ; ((DWORD)-10)
  (- (ash 1 (bitsizeof 'dword)) 10)
  "Handle to the standard input device.
Initially, this is a handle to the console input buffer, CONIN$.")
(defconstant STD_OUTPUT_HANDLE  ; ((DWORD)-11)
  (- (ash 1 (bitsizeof 'dword)) 11)
  "Handle to the standard output device.
Initially, this is a handle to the active console screen buffer, CONOUT$.")
(defconstant STD_ERROR_HANDLE   ; ((DWORD)-12)
  (- (ash 1 (bitsizeof 'dword)) 12)
  "Handle to the standard error device.
Initially, this is a handle to the active console screen buffer, CONOUT$.")

(def-call-out ReadFile (:return-type boolean)
  (:documentation "http://msdn.microsoft.com/library/en-us/fileio/fs/readfile.asp")
  (:arguments (hFile handle)
              (lpBuffer c-pointer)
	      (nNumberOfBytesToRead dword)
              (lpNumberOfBytesRead (c-ptr dword) :out)
	      (lpOverlapped c-pointer)))

(def-call-out WriteFile (:return-type boolean)
  (:documentation "http://msdn.microsoft.com/library/en-us/fileio/fs/writefile.asp")
  (:arguments (hFile handle)
              (lpBuffer c-pointer)
	      (nNumberOfBytesToWrite dword)
              (lpNumberOfBytesWritten (c-ptr dword) :out)
	      (lpOverlapped c-pointer)))

(def-call-out ReadConsoleA (:return-type boolean)
  (:documentation "http://msdn.microsoft.com/library/en-us/dllproc/base/readconsole.asp")
  (:arguments (hConsoleInput handle)
              (lpBuffer c-pointer)
              (nNumberOfCharsToRead dword)
              (lpNumberOfCharsRead (c-ptr dword) :out)
              (lpReserved c-pointer)))

(def-call-out WriteConsoleA (:return-type boolean)
  (:documentation "http://msdn.microsoft.com/library/en-us/dllproc/base/writeconsole.asp")
  (:arguments (hConsoleOutput handle)
              (lpBuffer c-pointer)
              (nNumberOfCharsToWrite dword)
              (lpNumberOfCharsWritten (c-ptr dword) :out)
              (lpReserved c-pointer)))

;; computer name
(eval-when (compile eval load)
  (defconstant MAX_COMPUTERNAME_LENGTH 16)) ; <winbase.h>

(def-call-out GetComputerNameA (:return-type boolean)
  (:arguments (buffer (c-ptr (c-array-max character #.MAX_COMPUTERNAME_LENGTH))
                      :out :alloca)
              (size (c-ptr dword) :in-out))) ; pass MAX_COMPUTERNAME_LENGTH

(def-c-enum COMPUTER_NAME_FORMAT
  ComputerNameNetBIOS
  ComputerNameDnsHostname
  ComputerNameDnsDomain
  ComputerNameDnsFullyQualified
  ComputerNamePhysicalNetBIOS
  ComputerNamePhysicalDnsHostname
  ComputerNamePhysicalDnsDomain
  ComputerNamePhysicalDnsFullyQualified
  ComputerNameMax)

(def-call-out GetComputerNameExA (:return-type boolean)
  (:arguments (type-name COMPUTER_NAME_FORMAT)
              (buffer (c-ptr (c-array-max character #.MAX_COMPUTERNAME_LENGTH))
                      :out :alloca)
              (size (c-ptr dword) :in-out))) ; pass MAX_COMPUTERNAME_LENGTH

;;;=================================== "user32.dll"
(default-foreign-library "user32.dll")

;;(c-lines "#include <winuser.h>~%")
(def-c-enum EWX                 ; shutdown operation
  (EWX_LOGOFF           #x0)
  (EWX_SHUTDOWN         #x1)
  (EWX_REBOOT           #x2)
  (EWX_FORCE            #x4)
  (EWX_POWEROFF         #x8)
  (EWX_FORCEIFHUNG     #x10))
(def-call-out ExitWindowsEx (:return-type boolean)
  (:arguments (flags uint)      ; EWX
              (reserved dword)))

(def-c-enum GR_OBJECTS GR_GDIOBJECTS GR_USEROBJECTS)
(def-call-out GetGuiResources (:return-type dword)
  (:arguments (process handle) (flags dword)))    ; GR_OBJECTS

;; create an icon
(def-c-enum image_type
  (IMAGE_BITMAP 0) IMAGE_ICON IMAGE_CURSOR IMAGE_ENHMETAFILE)
(def-c-enum load_options
  (LR_DEFAULTCOLOR 0)
  (LR_MONOCHROME 1)
  (LR_COLOR 2)
  (LR_COPYRETURNORG 4)
  (LR_COPYDELETEORG 8)
  (LR_LOADFROMFILE 16)
  (LR_LOADTRANSPARENT 32)
  (LR_LOADREALSIZE 128)
  (LR_LOADMAP3DCOLORS 4096)
  (LR_CREATEDIBSECTION 8192)
  (LR_COPYFROMRESOURCE #x4000)
  (LR_SHARED 32768))
(def-call-out LoadImageA (:return-type handle)
  (:documentation "http://msdn.microsoft.com/library/en-us/winui/winui/windowsuserinterface/resources/introductiontoresources/resourcereference/resourcefunctions/loadimage.asp")
  (:arguments (application-instance-handle handle)
              (image-name c-string)
              (type uint) (width int) (height int)
              (options int)))   ; load_options

(def-call-out DestroyIcon (:return-type boolean)
  (:documentation "http://msdn.microsoft.com/library/en-us/winui/winui/windowsuserinterface/resources/icons/iconreference/iconfunctions/destroyicon.asp")
  (:arguments (hIcon handle)))
#| example:
 (setq icon (win32:LoadImageA nil "d:\\gnu\\clisp\\current\\doc\\clisp.ico"
                              win32:IMAGE_ICON 0 0 win32:LR_LOADFROMFILE))
 (win32:DestroyIcon icon)
|#

;; buttons
(defconstant MB_OK 0)
(defconstant MB_OKCANCEL 1)
(defconstant MB_ABORTRETRYIGNORE 2)
(defconstant MB_YESNOCANCEL 3)
(defconstant MB_YESNO 4)
(defconstant MB_RETRYCANCEL 5)
(defconstant MB_CANCELTRYCONTINUE 6)
;; f1?
(defconstant MB_HELP #x4000)
;; icons
(defconstant MB_ICONEXCLAMATION #x30)
(defconstant MB_ICONWARNING #x30)
(defconstant MB_ICONINFORMATION 64)
(defconstant MB_ICONASTERISK 64)
(defconstant MB_ICONQUESTION 32)
(defconstant MB_ICONSTOP 16)
(defconstant MB_ICONERROR 16)
(defconstant MB_ICONHAND 16)
;; defaults
(defconstant MB_DEFBUTTON1 0)
(defconstant MB_DEFBUTTON2 256)
(defconstant MB_DEFBUTTON3 512)
(defconstant MB_DEFBUTTON4 #x300)
;; modality
(defconstant MB_APPLMODAL 0)
(defconstant MB_SYSTEMMODAL 4096)
(defconstant MB_TASKMODAL #x2000)

;; desktop
(defconstant MB_DEFAULT_DESKTOP_ONLY #x20000)

;; text
(defconstant MB_RIGHT #x80000)
(defconstant MB_RTLREADING #x100000)
(defconstant MB_SETFOREGROUND #x10000)
(defconstant MB_TOPMOST #x40000)
;; depends on windows version MB_SERVICE_NOTIFICATION
;; MB_SERVICE_NOTIFICATION_NT3X

(defconstant IDABORT 3 "Abort button was selected.")
(defconstant IDCANCEL 2 "Cancel button was selected.")
(defconstant IDCONTINUE 11 "Continue button was selected.")
(defconstant IDIGNORE 5 "Ignore button was selected.")
(defconstant IDNO 7 "No button was selected.")
(defconstant IDOK 1 "OK button was selected.")
(defconstant IDRETRY 4 "Retry button was selected.")
(defconstant IDTRYAGAIN 10 "Try Again button was selected.")
(defconstant IDYES 6 "Yes button was selected.")

(def-call-out MessageBoxA (:return-type int)
  (:arguments (parent handle) (text c-string) (caption c-string) (type uint))
  (:documentation "http://msdn.microsoft.com/library/en-us/winui/winui/windowsuserinterface/windowing/dialogboxes/dialogboxreference/dialogboxfunctions/messagebox.asp"))
#| examples:
 (win32:MessageBoxA nil "welcome to clisp" "message from clisp" win32:MB_OK)
 (win32:MessageBoxA nil "welcome to clisp" "message from clisp"
                    (logior win32:MB_YESNOCANCEL win32:MB_ICONWARNING))
|#

;; http://msdn.microsoft.com/library/en-us/winui/winui/windowsuserinterface/dataexchange/clipboard/clipboardreference/clipboardfunctions/getclipboarddata.asp
(def-call-out OpenClipboard (:return-type boolean)
  (:arguments (hWndNewOwner handle)))
(def-call-out CloseClipboard (:return-type boolean) (:arguments))
(def-call-out EmptyClipboard (:return-type boolean) (:arguments))
(def-call-out EnumClipboardFormats (:return-type uint)
  (:arguments (format uint)))
(def-call-out GetClipboardData (:return-type handle) (:arguments (format uint)))
(def-call-out GetClipboardFormatNameA (:return-type int)
  (:arguments (format uint)
              (buffer (c-ptr (c-array-max character #.BUFSIZ)) :out :alloca)
              (size int))) ; always pass BUFSIZ as the second argument
(def-call-out GetClipboardOwner (:return-type handle) (:arguments))
(def-call-out GetClipboardSequenceNumber (:return-type dword) (:arguments))
(def-call-out GetClipboardViewer (:return-type handle) (:arguments))
(def-call-out GetOpenClipboardWindow (:return-type handle) (:arguments))
(def-call-out GetPriorityClipboardFormat (:return-type int)
  (:arguments (formats (c-array-max uint #.BUFSIZ)) (size int)))
(def-call-out IsClipboardFormatAvailable (:return-type boolean)
  (:arguments (format uint)))
(def-call-out RegisterClipboardFormat (:return-type uint)
  (:arguments (format c-string)))
(def-call-out RemoveClipboardFormatListener (:return-type boolean)
  (:arguments (hwnd handle)))
(def-call-out SetClipboardData (:return-type handle)
  (:arguments (format uint) (data handle)))
(def-call-out SetClipboardViewer (:return-type handle)
  (:arguments (hwnd handle)))

;;;===================================== "advapi32.dll"
(default-foreign-library "advapi32.dll")
;; user name
(eval-when (compile eval load) (defconstant UNLEN 256)) ; <lmcons.h>
(def-call-out GetUserNameA (:return-type boolean)
  (:arguments (buffer (c-ptr (c-array-max character #.UNLEN)) :out :alloca)
              (size (c-ptr dword) :in-out))) ; pass UNLEN

;;;==================================== "secur32.dll"
(default-foreign-library "secur32.dll")

;; declared in <secext.h>, include <security.h>
(def-c-enum EXTENDED_NAME_FORMAT
  (NameUnknown 0)
  (NameFullyQualifiedDN 1)
  (NameSamCompatible 2)
  (NameDisplay 3)
  (NameUniqueId 6)
  (NameCanonical 7)
  (NameUserPrincipal 8)
  (NameCanonicalEx 9)
  (NameServicePrincipal 10))
(def-call-out GetUserNameExA (:return-type boolean)
  (:arguments (name-format EXTENDED_NAME_FORMAT)
              (buffer (c-ptr (c-array-max character #.UNLEN)) :out :alloca)
              (size (c-ptr ulong) :in-out))) ; pass UNLEN
(def-call-out GetComputerObjectNameA (:return-type boolean)
  (:arguments (name-format EXTENDED_NAME_FORMAT)
              (buffer (c-ptr (c-array-max character #.UNLEN)) :out :alloca)
              (size (c-ptr ulong) :in-out))) ; pass UNLEN

;;;==================================== "shell32.dll"
(default-foreign-library "shell32.dll")
;; http://msdn.microsoft.com/library/en-us/shellcc/platform/shell/reference/functions/shellexecute.asp
(def-c-enum SE_ERROR            ; <shellapi.h>
  (SE_ERR_FNF 2)
  (SE_ERR_PNF 3)
  (SE_ERR_ACCESSDENIED 5)
  (SE_ERR_OOM 8)
  (SE_ERR_DLLNOTFOUND 32)
  (SE_ERR_SHARE 26)
  (SE_ERR_ASSOCINCOMPLETE 27)
  (SE_ERR_DDETIMEOUT 28)
  (SE_ERR_DDEFAIL 29)
  (SE_ERR_DDEBUSY 30)
  (SE_ERR_NOASSOC 31))
(def-c-enum SHOW_COMMAND        ; <winuser.h>
  (SW_HIDE 0)
  (SW_NORMAL 1)
  (SW_SHOWNORMAL 1)
  (SW_SHOWMINIMIZED 2)
  (SW_MAXIMIZE 3)
  (SW_SHOWMAXIMIZED 3)
  (SW_SHOWNOACTIVATE 4)
  (SW_SHOW 5)
  (SW_MINIMIZE 6)
  (SW_SHOWMINNOACTIVE 7)
  (SW_SHOWNA 8)
  (SW_RESTORE 9)
  (SW_SHOWDEFAULT 10)
  (SW_FORCEMINIMIZE 11)
  (SW_MAX 11))
(def-call-out ShellExecuteA (:return-type int)
  (:arguments (parent handle) (operation c-string) (file c-string)
              (parameters c-string) (directory c-string) (show SHOW_COMMAND)))

;; ==========================================================================

(pushnew "WIN32" custom:*system-package-list* :test #'string=)
(provide "win32")
