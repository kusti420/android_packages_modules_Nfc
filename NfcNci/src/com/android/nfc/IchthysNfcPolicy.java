/*
 * Copyright (C) 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.nfc;

import android.app.role.RoleManager;
import android.content.ComponentName;
import android.content.Context;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.ResolveInfo;
import android.nfc.Constants;
import android.os.Binder;
import android.os.Process;
import android.os.UserHandle;
import android.provider.Settings;
import android.text.TextUtils;
import android.util.Log;

import java.util.ArrayList;
import java.util.List;

/**
 * IchthysOS: per-app NFC block.
 *
 * <p>The {@code NFC} permission is a normal permission, so every app that asks for it gets tag
 * reads and host card emulation with no prompt. Apps named in the per-user {@link
 * Settings.Secure} list {@link #BLOCKED_PACKAGES_SETTING} lose both:
 * <ul>
 *   <li><b>Tag dispatch</b> — {@code NfcDispatcher} drops them from the NDEF / TECH / TAG
 *       activity resolution and from AAR launches, and {@code NfcService} ignores their
 *       foreground-dispatch, reader-mode and discovery-technology requests (the same silent
 *       return stock uses for a caller that is not in the foreground).
 *   <li><b>Card emulation</b> — {@code RegisteredServicesCache} and
 *       {@code RegisteredNfcFServicesCache} skip their HCE / off-host / HCE-F services, so no AID
 *       or system code is routed to them and they are never bound. The caches are re-validated
 *       when the list changes.
 * </ul>
 *
 * <p><b>Never blocked</b>, even if listed: the default payment app (the {@code
 * nfc_payment_default_component} holder and the Wallet role holder), core system UIDs,
 * preinstalled and platform-signed apps, and holders of the standard default-app roles.
 */
public final class IchthysNfcPolicy {

    private static final String TAG = "IchthysNfcPolicy";

    /**
     * Per-user {@link Settings.Secure} key: comma-separated package names whose NFC access is
     * blocked. Unset or empty blocks nothing. Written by Ichthys Guard.
     */
    public static final String BLOCKED_PACKAGES_SETTING = "ichthys_nfc_blocked_pkgs";

    /** Default-app roles whose holders are never blocked, matched by name. */
    private static final String[] EXEMPT_ROLES = {
        "android.app.role.WALLET",
        "android.app.role.ASSISTANT",
        "android.app.role.BROWSER",
        "android.app.role.DIALER",
        "android.app.role.SMS",
        "android.app.role.EMERGENCY",
        "android.app.role.HOME",
        "android.app.role.CALL_REDIRECTION",
        "android.app.role.CALL_SCREENING",
        "android.app.role.NOTES",
    };

    private IchthysNfcPolicy() {}

    /** Whether any package running as {@code uid} is blocked. Never throws. */
    public static boolean isUidBlocked(Context context, int uid) {
        if (UserHandle.getAppId(uid) < Process.FIRST_APPLICATION_UID) {
            return false;
        }
        final UserHandle user = UserHandle.getUserHandleForUid(uid);
        final long token = Binder.clearCallingIdentity();
        try {
            final Context userContext = context.createContextAsUser(user, 0);
            final String[] packages = userContext.getPackageManager().getPackagesForUid(uid);
            if (packages == null) {
                return false;
            }
            for (String packageName : packages) {
                if (isBlockedInternal(userContext, user, packageName)) {
                    return true;
                }
            }
            return false;
        } catch (RuntimeException e) {
            Log.w(TAG, "Failed to evaluate NFC block for uid " + uid, e);
            return false;
        } finally {
            Binder.restoreCallingIdentity(token);
        }
    }

    /** Whether {@code packageName} in {@code userId} is blocked. Never throws. */
    public static boolean isPackageBlocked(Context context, String packageName, int userId) {
        if (TextUtils.isEmpty(packageName)) {
            return false;
        }
        final UserHandle user = UserHandle.of(userId);
        final long token = Binder.clearCallingIdentity();
        try {
            return isBlockedInternal(context.createContextAsUser(user, 0), user, packageName);
        } catch (RuntimeException e) {
            Log.w(TAG, "Failed to evaluate NFC block for " + packageName, e);
            return false;
        } finally {
            Binder.restoreCallingIdentity(token);
        }
    }

    /**
     * @return {@code activities} without those belonging to blocked packages in {@code userId};
     *     the same list instance when nothing was removed
     */
    public static List<ResolveInfo> filterActivities(Context context,
            List<ResolveInfo> activities, int userId) {
        if (activities == null || activities.isEmpty() || isListEmpty(context, userId)) {
            return activities;
        }
        List<ResolveInfo> filtered = null;
        for (int i = 0; i < activities.size(); i++) {
            ResolveInfo info = activities.get(i);
            boolean blocked = info.activityInfo != null
                    && isPackageBlocked(context, info.activityInfo.packageName, userId);
            if (blocked && filtered == null) {
                filtered = new ArrayList<>(activities.subList(0, i));
            } else if (!blocked && filtered != null) {
                filtered.add(info);
            }
            if (blocked) {
                Log.i(TAG, "Tag dispatch skipped for blocked " + info.activityInfo.packageName);
            }
        }
        return filtered != null ? filtered : activities;
    }

    private static boolean isListEmpty(Context context, int userId) {
        final long token = Binder.clearCallingIdentity();
        try {
            return TextUtils.isEmpty(Settings.Secure.getString(
                    context.createContextAsUser(UserHandle.of(userId), 0).getContentResolver(),
                    BLOCKED_PACKAGES_SETTING));
        } catch (RuntimeException e) {
            return true;
        } finally {
            Binder.restoreCallingIdentity(token);
        }
    }

    /** Caller has cleared the calling identity. */
    private static boolean isBlockedInternal(Context userContext, UserHandle user,
            String packageName) {
        if (!isListed(userContext, packageName)) {
            return false;
        }
        return !isExempt(userContext, user, packageName);
    }

    private static boolean isListed(Context userContext, String packageName) {
        final String value = Settings.Secure.getString(
                userContext.getContentResolver(), BLOCKED_PACKAGES_SETTING);
        if (TextUtils.isEmpty(value)) {
            return false;
        }
        for (String entry : value.split(",")) {
            if (packageName.equals(entry.trim())) {
                return true;
            }
        }
        return false;
    }

    private static boolean isExempt(Context userContext, UserHandle user, String packageName) {
        // The default payment app is never blocked: tapping to pay must keep working.
        final String paymentDefault = Settings.Secure.getString(userContext.getContentResolver(),
                Constants.SETTINGS_SECURE_NFC_PAYMENT_DEFAULT_COMPONENT);
        final ComponentName payment = paymentDefault == null
                ? null : ComponentName.unflattenFromString(paymentDefault);
        if (payment != null && packageName.equals(payment.getPackageName())) {
            return true;
        }
        final PackageManager pm = userContext.getPackageManager();
        try {
            final ApplicationInfo info = pm.getApplicationInfo(packageName, 0);
            if (UserHandle.getAppId(info.uid) < Process.FIRST_APPLICATION_UID
                    || (info.flags & (ApplicationInfo.FLAG_SYSTEM
                            | ApplicationInfo.FLAG_UPDATED_SYSTEM_APP)) != 0) {
                return true;
            }
            if (pm.checkSignatures(info.uid, Process.SYSTEM_UID)
                    == PackageManager.SIGNATURE_MATCH) {
                return true;
            }
        } catch (PackageManager.NameNotFoundException e) {
            return false;
        }
        final RoleManager roleManager = userContext.getSystemService(RoleManager.class);
        if (roleManager == null) {
            return false;
        }
        for (String role : EXEMPT_ROLES) {
            try {
                final List<String> holders = roleManager.getRoleHoldersAsUser(role, user);
                if (holders != null && holders.contains(packageName)) {
                    return true;
                }
            } catch (RuntimeException e) {
                // Unknown role on this build, or role service not ready yet.
            }
        }
        return false;
    }
}
