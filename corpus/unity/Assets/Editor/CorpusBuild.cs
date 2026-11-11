using System;
using System.IO;
using UnityEditor;
using UnityEditor.Build.Reporting;
using UnityEditor.SceneManagement;
using UnityEngine;

public static class CorpusBuild
{
    public static void Android()
    {
        if (Application.unityVersion != "2022.3.62f2")
            throw new InvalidOperationException("需要 Unity 2022.3.62f2");
        var args = Environment.GetCommandLineArgs();
        int index = Array.IndexOf(args, "-corpusOut");
        if (index < 0 || index + 1 == args.Length)
            throw new ArgumentException("缺少 -corpusOut");
        string output = args[index + 1];
        Directory.CreateDirectory(output);
        const string scenePath = "Assets/Main.unity";
        var scene = EditorSceneManager.NewScene(NewSceneSetup.EmptyScene, NewSceneMode.Single);
        EditorSceneManager.SaveScene(scene, scenePath);
        const BuildTargetGroup group = BuildTargetGroup.Android;
        EditorUserBuildSettings.SwitchActiveBuildTarget(group, BuildTarget.Android);
        PlayerSettings.SetScriptingBackend(group, ScriptingImplementation.IL2CPP);
        PlayerSettings.SetIl2CppCompilerConfiguration(group, Il2CppCompilerConfiguration.Release);
        PlayerSettings.SetManagedStrippingLevel(group, ManagedStrippingLevel.Minimal);
        PlayerSettings.SetApplicationIdentifier(group, "org.corpus.il2cpp");
        PlayerSettings.Android.targetArchitectures = AndroidArchitecture.ARM64 | AndroidArchitecture.X86_64;
        PlayerSettings.SetAdditionalIl2CppArgs("--enable-divide-by-zero-check");
        EditorUserBuildSettings.androidCreateSymbols = AndroidCreateSymbols.Debugging;
        EditorUserBuildSettings.exportAsGoogleAndroidProject = false;
        var report = BuildPipeline.BuildPlayer(new BuildPlayerOptions {
            scenes = new[] { scenePath }, locationPathName = Path.Combine(output, "corpus.apk"),
            target = BuildTarget.Android, targetGroup = group, options = BuildOptions.None
        });
        var summary = report.summary;
        File.WriteAllText(Path.Combine(output, "build-report.txt"),
            $"unity={Application.unityVersion}\nconfiguration=Release\narchitectures=ARM64,X86_64\n" +
            $"result={summary.result}\nerrors={summary.totalErrors}\nwarnings={summary.totalWarnings}\ntime={summary.totalTime}\n");
        EditorApplication.Exit(summary.result == BuildResult.Succeeded ? 0 : 1);
    }
}
