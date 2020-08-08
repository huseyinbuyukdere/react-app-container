import React from 'react';
interface MenuItemProps {
    label: string;
    onClick: (routeKey?: string) => void;
    iconComp?: any;
    iconName?: string;
    iconCompStyle?: React.CSSProperties;
    rightIconComp?: any;
    rightIconName?: string;
    rightIconCompStyle?: React.CSSProperties;
    style?: React.CSSProperties;
    isSelected: boolean;
    isFlat?: boolean;
}
export default function MenuItem(props: MenuItemProps): JSX.Element;
export {};
