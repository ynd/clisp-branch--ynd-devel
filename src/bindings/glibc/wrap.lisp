;;; Lisp wrappers for the GLIBC FFI

(require "linux")

(in-package "LINUX")

;; if you think you need this, you should use (array character)
;; instead of (array char)
;;(defun vec2string (vec)
;;  ;; Convert a char[] to a lisp STRING.
;;  (convert-string-from-bytes vec *foreign-encoding*
;;                             :end (position 0 vec)))

(defun linux-error (caller)
  (error "~s: ~a" caller (strerror errno)))
(defmacro check-res (res caller)
  `(unless (zerop ,res) (linux-error ,caller)))

(defun real-path (name)
  (multiple-value-bind (success resolved)
      ;; :out or :in-out parameters are returned via multiple values
      (realpath name)
    (unless success (linux-error 'real-path))
    resolved))

(defun get-host-name ()
  (multiple-value-bind (success name)
      ;; :out or :in-out parameters are returned via multiple values
      (gethostname MAXHOSTNAMELEN)
    (check-res success 'get-host-name)
    name))

(defun get-domain-name ()
  (multiple-value-bind (success name)
      ;; :out or :in-out parameters are returned via multiple values
      (getdomainname MAXHOSTNAMELEN)
    (check-res success 'get-domain-name)
    name))

;; convenience functions for ffi sigaction definitions
;; Peter Wood 2002

(defun signal-valid-p (signal)
  "Is SIGNAL valid for this machine?"
  (zerop (sigaction-new signal nil nil)))

(defun signal-action-retrieve (signal)
  "Return the presently installed sigaction structure for SIGNAL"
  (multiple-value-bind (ret act) (sigaction-old signal nil)
    (check-res ret 'signal-action-retrieve)
    act))

(defun signal-action-install (signal newact)
  "Install NEWACT as the sigaction structure for SIGNAL. Error on failure."
  (check-res (sigaction-new signal newact nil) 'signal-action-install))

(defun sa-handler (sigact)
  "Returns the signal handler function for SIGACT struct. SETF place."
  (slot-value sigact 'sa_handler))
(defsetf sa-handler (sigact) (handler)
  `(setf (slot-value ,sigact 'sa_handler) ,handler))

(defun sa-flags (sigact)
  "Returns the sa_flags for SIGACT struct. SETF place."
  (slot-value sigact 'sa_flags))
(defsetf sa-flags (sigact) (newflags)
  `(setf (slot-value ,sigact 'sa_flags) ,newflags))

;; e.g.: (setf (sa-flags SIGACT) (logior SA_RESETHAND SA_NOCLDSTOP))

(defun sa-mask (sigact)
  "Returns the sa_mask for SIGACT struct. SETF place."
  (slot-value sigact 'sa_mask))
(defsetf sa-mask (sigact) (mask)
  `(setf (slot-value ,sigact 'sa_mask) ,mask))

(defun sigset-empty ()
  "Return an empty sigset."
  (multiple-value-bind (ret act) (sigemptyset)
    (check-res ret 'sigset-empty)
    act))

(defun sigset-fill ()
  "Return a full sigset"
  (multiple-value-bind (ret set) (sigfillset)
    (check-res ret 'sigset-fill)
    set))

(defun sigset-add (set signal)
  "Return a new set with SIGNAL"
  (multiple-value-bind (ret set) (sigaddset set signal)
    (check-res ret 'sigset-add)
    set))

(defun sigset-del (set signal)
  "Return a new set without SIGNAL"
  (multiple-value-bind (ret set) (sigdelset set signal)
    (check-res ret 'sigset-del)
    set))

(defun sigset-member-p (set signal)
  "T if SIGNAL is a member of SET, otherwise NIL"
  (not (zerop (sigismember set signal))))

(defun set-sigprocmask (act set)
  ;; NB the result of this will not be 'visible' in the sigaction
  ;; struct which contains SET, although the ACT *will* be performed.
  ;; If you want a visible result, see sigprocmask-set-n-save,
  ;; which returns as 2nd value the set structure resulting from ACT.
  "Do ACT on SET. Returns NIL on success and signals an error on failure."
  (check-res (sigprocmask-set act set nil) 'set-sigprocmask))

(defun sigset-pending ()
  "Returns the set of pending signals. Nil on failure"
  (multiple-value-bind (ret set) (sigpending)
    (check-res ret 'sigset-pending)
    set))

(defun set-signal-handler (signal fn)
  "Sets FN as signal handler for SIGNAL.  Returns old signal handler."
  (let* ((sigact (signal-action-retrieve signal)) ; the current sigact
         (oh (sa-handler sigact))) ; save the old handler to return
    (setf (sa-handler sigact) fn) ; make fn be the handler in sigact
    (signal-action-install signal sigact) ; install
    oh))                        ; return the old handler

(pushnew "LINUX" custom:*system-package-list* :test #'string=)
